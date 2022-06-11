--[[
      Lua implementation of relmetric
--]]

-- set up as a module
local M = {}

-- ENVIRONMENT VARIABLE: CHK_WT_BOTH_DIRS
-- whether to check min weight in both directions or rely on Property 2 that
--   if #Y1<=#Y2, then distance(R1,R2) = min weight(g|Y1-Y2))
M.CHK_WT_BOTH_DIRS = os.getenv("CHK_WT_BOTH_DIRS") or false

--[[
  /* A Relation is represented via an array of Columns.,
  * Each Column is represented by a list of integers,
  * in big-endian order, and a count of rows.
  * Columns end on word boundaries; so modulus reside in
  * low end of final for each column.
  */
  --]]

  -- Bit encoding
  -- Export only M.MAX_INT, M.INT_SIZE, M.ROWS_PER_UNSIGNED

  -- M.MAX_INT = math.maxinteger -- Lua integer (usually long long)
  M.MAX_INT = 0xffff -- unsigned short
  M.INT_SIZE = 4 * #string.format('%X', M.MAX_INT)
  M.ROWS_PER_UNSIGNED = M.INT_SIZE
  local ROW_MASK = {}
  ROW_MASK[M.ROWS_PER_UNSIGNED] = 0x1
  for i = M.ROWS_PER_UNSIGNED, 2, -1 do
    ROW_MASK[i - 1] = ROW_MASK[i] << 1
  end
  -- PACK_FORMAT = '>J'  -- big-endian unsigned Lua integers (usually long long)

--[[
  /* Column creation and methods */
--]]

-- new creates a new Column with fields row_count, bits
-- Input: nil or table of fields row_count and bits
--        row_count is the count of rows / bits in the column
--        bits is a table of integers in big-endian order
--        whose bits each represent one element of the relation
-- Output: Column with fields from input or default Column

-- default Column
M.Column = {row_count = 0, bits = {}}

function M.Column:new(obj)
  local newObj
  if obj then
    assert(math.tointeger(obj.row_count) and math.tointeger(obj.row_count) >= 0, "Column:new: row_count must a non-negative integer but got: "..tostring(obj.row_count))
    -- assert(type(obj.bits) == "string", "Column:new bits must be a packed string but got: "..tostring(obj.bits))
    assert(type(obj.bits) == "table", "Column:new: bits must be a table of integers or empty table but got: "..tostring(obj.bits))
    for _,o in ipairs(obj.bits) do
      assert(math.tointeger(o) and math.tointeger(o) <= M.MAX_INT, "Column:new: takes integers but got: "..tostring(o))
    end
    newObj = {
      row_count = obj.row_count,
      bits = obj.bits
    }
  else
    newObj = {
      row_count = M.Column.row_count,
      -- bits = string.pack(PACK_FORMAT,0x0)
      bits = M.Column.bits
    }
  end
  self.__index = self
  return setmetatable(newObj, self)
end

-- fromints creates a Column from integers (2 bytes), inferring the row_count
-- Input (vararg):  table of integers or unpacked table thereof
-- Output:  Column
function M.Column:fromints(...)
  local input = {...}
  if #input == 1 and type(input[1]) == "table" then
    input = input[1]
  end

  for _,o in ipairs(input) do
    assert(math.tointeger(o) and math.tointeger(o) <= M.MAX_INT, "Column.fromints: takes integers or table of them (or empty table) but got: "..tostring(o))
  end

  return M.Column:new({
    row_count = M.ROWS_PER_UNSIGNED * #input,
    -- bits = string.pack(string.rep(PACK_FORMAT, #input),...)
    bits = input
  })
end

-- toints converts a Column into integers (2 bytes)
function M.Column:toints()
  -- local n = self.row_count // M.ROWS_PER_UNSIGNED
  -- if self.row_count % 8 > 0 then n = n + 1 end
  -- local res= {string.unpack(string.rep(PACK_FORMAT, n), self.bits)}
  -- -- remove and ignore last element from string.unpack
  -- table.remove(res, #res)
  -- return table.unpack(res)
  return table.unpack(self.bits)
end

-- generate a string that prints vertically, most-to-least significant
function M.Column:__tostring()
  local whole_ints = self.row_count // M.ROWS_PER_UNSIGNED
  local rest_bits = self.row_count % 8
  local ints = {self:toints()}
  local res = ""
  -- first the whole bytes
  for i = 1, whole_ints do
    for j = 1, #ROW_MASK do
      if ints[i] & ROW_MASK[j] > 0 then
        res = res..string.format("%s\n",'1')
      else
        res = res..string.format("%s\n",'0')
      end
    end
  end
  -- now the rest
  for j = (9 - rest_bits), 8 do  -- ignores if r == 0
    if ints[whole_ints + 1] & ROW_MASK[j] > 0 then
      res = res..string.format("%s\n",'1')
    else
      res = res..string.format("%s\n",'0')
    end
  end
  res = res..string.format("\n")
  return res
end

-- equality of Columns
function M.Column:__eq(obj)
  assert(type(obj) == "table" and type(obj.row_count) == "number", "Column:__eq takes Columns but got: "..tostring(obj))
  local res = true
  if self.row_count ~= obj.row_count then
    res = false
  else
    local ints1 = {self:toints()}
    local ints2 = {obj:toints()}
    if #ints1 ~= #ints2 then
      res = false
    else
      for i = 1, #ints1 do
        if ints1[i] ~= ints2[i] then
          res = false
        end
      end
    end
  end
  return res
end

-- less than or equal for Columns
function M.Column:__le(obj)
  assert(type(obj) == "table" and type(obj.row_count) == "number", "Column:__le takes Columns but got: "..tostring(obj))
  assert(self.row_count == obj.row_count, "Column:__le requires Columns of equal row_count but: "..tostring(obj.row_count).." ~= "..tostring(self.row_count))
  local ints1 = {self:toints()}
  local ints2 = {obj:toints()}
  assert(#ints1 == #ints2, "Column:__le requires Columns of equal length but: "..tostring(#ints1).." ~= "..tostring(#ints2))
  local res = true
  for i = 1, #ints1 do
    if ints1[i] > ints2[i] then
      res = false
    end
  end
  return res
end

-- less than for Columns
function M.Column:__lt(obj)
  assert(type(obj) == "table" and type(obj.row_count) == "number", "Column:__lt takes Columns but got: "..tostring(obj))
  assert(self.row_count == obj.row_count, "Column:__lt requires Columns of equal row_count but: "..tostring(obj.row_count).." ~= "..tostring(self.row_count))
  local ints1 = {self:toints()}
  local ints2 = {obj:toints()}
  assert(#ints1 == #ints2, "Column:__lt requires Columns of equal length but: "..tostring(#ints1).." ~= "..tostring(#ints2))
  local res = false
  for i = 1, #ints1 do
    if ints1[i] < ints2[i] then
      res = true
    end
  end
  return res
end

-- __band for Columns
function M.Column:__band(obj)
  assert(type(obj) == "table" and type(obj.row_count) == "number", "Column:__band takes Columns but got: "..tostring(obj))
  assert(self.row_count == obj.row_count, "Column:__band requires Columns of equal row_count but: "..tostring(obj.row_count).." ~= "..tostring(self.row_count))
  local ints1 = {self:toints()}
  local ints2 = {obj:toints()}
  assert(#ints1 == #ints2, "Column:__band requires Columns of equal length but: "..tostring(#ints1).." ~= "..tostring(#ints2))
  local res = {}
  for i = 1, #ints1 do
    res[i] = ints1[i] & ints2[i]
  end
  return res
end

-- __bor for Columns
function M.Column:__bor(obj)
  assert(type(obj) == "table" and type(obj.row_count) == "number", "Column:__bor takes Columns but got: "..tostring(obj))
  assert(self.row_count == obj.row_count, "Column:__bor requires Columns of equal row_count but: "..tostring(obj.row_count).." ~= "..tostring(self.row_count))
  local ints1 = {self:toints()}
  local ints2 = {obj:toints()}
  assert(#ints1 == #ints2, "Column:__bor requires Columns of equal length but: "..tostring(#ints1).." ~= "..tostring(#ints2))
  local res = {}
  for i = 1, #ints1 do
    res[i] = ints1[i] | ints2[i]
  end
  return res
end

-- any_joint_row checks whether two Columns share a relation in any row
-- Input:  obj = a Column
-- Output: boolean whether input and self share a relation in any row
function M.Column:any_joint_col(obj)
  assert(type(obj) == "table" and type(obj.row_count) == "number", "Column:any_joint_row takes Columns but got: "..tostring(obj))
  assert(self.row_count == obj.row_count, "Column:any_joint_row requires Columns of equal row_count but: "..tostring(obj.row_count).." ~= "..tostring(self.row_count))
  local ints1 = {self:toints()}
  local ints2 = {obj:toints()}
  assert(#ints1 == #ints2, "Column:any_joint_row requires Columns of equal length but: "..tostring(#ints1).." ~= "..tostring(#ints2))
  local res = false
  local i = 1
  while not res and i <= #ints1 do
    res = (ints1[i] & ints2[i] > 0)
  end
  return res
end

--[[
 /* Count the number of differences between two columns
 * Input: second column to which self is to be compared
 * Returns: difference count
 */
--]]
function M.Column:column_diff(obj)
  assert(type(obj) == "table" and type(obj.row_count) == "number" and type(obj.bits) == "table", "Column:column_diff: takes a Column but got: "..tostring(obj))
  assert(self.row_count == obj.row_count or #self.bits == 0 or #obj.bits == 0, "Column:column_diff: row_counts must be the same for non-empty Column but: "..tostring(self.row_count).." ~= "..tostring(obj.row_count))
  local diff, c1, c2, current_diff, whole_ints, rest_bits
  if #self.bits == 0 then
    diff = #obj.bits
  elseif #obj.bits == 0 then
    diff = #self.bits
  else
    whole_ints = self.row_count // M.ROWS_PER_UNSIGNED
    rest_bits = self.row_count % 8
    c1 = {self:toints()}
    c2 = {obj:toints()}
    diff = 0

    -- unpack whole words
    for i = 1, whole_ints do
      current_diff = c1[i] ~ c2[i]
      for j = 1, M.ROWS_PER_UNSIGNED do
        diff = diff + (current_diff & 0x01)
        current_diff = current_diff >> 1
      end
    end

    -- collect remaining rows
    if rest_bits > 0 then
      current_diff = c1[#c1] ~ c2[#c2]
      for i = 1, rest_bits do
        diff = diff + (current_diff & 0x01)
        current_diff = current_diff >> 1
      end
    end
  end
  return diff
end

--[[
  /* Relation creation and methods */
--]]

-- default Relation
M.Relation = {row_count = 0, column_count = 0, bitfield = {}}

-- new creates a new Relation with fields row_count, column_count, bitfield
-- Input: nil or table of fields row_count, column_count, bitfield
--        row_count is the (positive integer) row_count of all Columns in bitfield
--        column_count is a positive integer
--        bitfield is a table of Columns
-- Output: Column with fields from Input or default Column
function M.Relation:new(obj)
  local newObj = {}
  if obj then
    assert(type(obj) == "table", "Relation:new: takes {row_count, column_count, bitfield} or nothing but got: "..tostring(obj))
    assert(math.tointeger(obj.row_count) and obj.row_count >= 0, "Relation:new: row_count must be a non-negative integer but got: "..tostring(obj.row_count))
    assert(math.tointeger(obj.column_count) and obj.column_count >= 0, "Relation:new: column_count must be a non-negative integer but got: "..tostring(obj[1]))
    assert(type(obj.bitfield) == "table", "Relation:new: bitfield must be a (maybe empty) table of Columns but got: "..tostring(obj))
    for i = 1, #obj.bitfield do
      -- assert(type(obj.bitfield[i]) == "table" and obj.bitfield[i].row_count and obj.bitfield[i].bits, "Relation:new bifields must be a table of columns but got element "..tostring(i)..": "..tostring(obj.bitfield[i]))
      M.Column:new(obj.bitfield[i]) -- just to check validity
    end
    newObj = {
      row_count = obj.row_count,
      column_count = obj.column_count,
      bitfield = obj.bitfield
    }
  else
    newObj = {
      row_count = M.Relation.row_count,
      column_count = M.Relation.column_count,
      bitfield = M.Relation.bitfield
    }
  end
  self.__index = self
  return setmetatable(newObj, self)
end

-- fromcols creates a relation from Columns, inferring the row_count, column_count
-- Inputs (vararg): table of Columns or unpacked table thereof
-- Output: Relation of the input Columns with row_count = #col1_row_count
function M.Relation:fromcols(...)
  local input = {...}
  if #input == 1 and type(input[1]) == "table" and not input[1].bits then
    input = input[1]
  end
  assert(type(input[1]) == "table" and math.tointeger(input[1].row_count), "Relation:fromcols takes Columns or a (maybe empty) list of them but got: "..tostring(input[1]))
  local col1_row_count = input[1].row_count
  for _, o in ipairs(input) do
    assert(type(o) == "table" and o.row_count and o.bits, "Relation:fromcols takes Columns or a (maybe empty) list of them but got: "..tostring(o))
    assert(o.row_count == col1_row_count, "Relation:fromcols requires same row_count for all input Columns but: "..tostring(o.row_count).." ~= "..tostring(col1_row_count))
  end
  return M.Relation:new({
    row_count = col1_row_count,
    column_count = #input,
    bitfield = input
  })
end

-- tocols returns the Columns of a Relation
function M.Relation:tocols()
  return table.unpack(self.bitfield)
end

-- fromints creates a relation from tables of integers representing columns
-- Inputs (vararg): table or unpacked table of tables of integers
-- Output: Relation of the input Columns with row_count inferred
function M.Relation:fromints(...)
  local input = {...}
  if #input == 1 and type(input[1]) == "table" and type(input[1][1]) == "table" then
    input = input[1]
  end
  assert(type(input[1]) == "table", "Relation:fromints: takes tables of integers but got: "..tostring(o))
  local col1_int_count = #input[1] or error("Relation:fromints: takes tables of integers but got: "..tostring(input[1]))
  local bf = {}
  for i, o in ipairs(input) do
    assert(type(o) == "table", "Relation:fromints: takes tables of integers but got: "..tostring(o))
    assert(#o == col1_int_count, "Relation:fromints: requires equal-length tables of integers but got: "..tostring(#o).." ~= "..tostring(col1_int_count))
    bf[i] = M.Column:fromints(o)
  end
  return M.Relation:new({
    row_count = bf[1].row_count,
    column_count = #bf,
    bitfield = bf
  })
end

-- toints returns the tables of integers representing columns
function M.Relation:toints()
  local res = {}
  for i, c in ipairs(self.bitfield) do
    res[i] = {c:toints()}
  end
  return table.unpack(res)
end

-- generate a string that prints out a relation
function M.Relation:__tostring()
  local whole_ints = self.row_count // M.ROWS_PER_UNSIGNED
  local rest_bits = self.row_count % 8
  local cols = {}
  local res = ""
  for i, c in ipairs(self.bitfield) do
    cols[i] = {c:toints()}
  end
  -- first the whole bytes
  for i = 1, whole_ints do
    for j = 1, #ROW_MASK do
      for k = 1, self.column_count do
        if cols[k][i] & ROW_MASK[j] > 0 then
          res = res..string.format("%s",'1')
        else
          res = res..string.format("%s",'0')
        end
      end
      res = res..string.format("\n")
    end
  end
  -- now the rest
  for j = (#ROW_MASK + 1 - rest_bits), #ROW_MASK do  -- ignores if r >= #ROW_Mask
    for k = 1, self.column_count do
      if cols[k][whole_ints + 1] & ROW_MASK[j] > 0 then
        res = res..string.format("%s",'1')
      else
        res = res..string.format("%s",'0')
      end
    end
    res = res..string.format("\n")
  end
  return res
end

-- __sub one-for-one removes identical columns from self found in input
-- Input:  obj = a Relation
-- Output: a new Relation
function M.Relation:__sub(obj)
  assert(type(obj) == "table" and type(obj.row_count) == "number" and type(obj.column_count) == "number" and type(obj.bitfield) == "table", "Relation:__sub: takes a Relation but got: "..tostring(obj))
  assert(self.row_count == obj.row_count, "Column:__sub: row_counts must be the same but: "..tostring(self.row_count).." ~= "..tostring(obj.row_count))
  local new_cols = {}
  local res
  for _, self_col in ipairs(self.bitfield) do
    for _, obj_col in ipairs(obj.bitfield) do
      if self_col == obj_col then
        break
      else
        new_cols[#new_cols+1] = self_col
      end
    end
  end
  print(string.format('rel1 - rel2 found: %s cols',#new_cols))
  res = M.Relation:fromcols(new_cols)
  res.row_count = self.row_count
  return res
end

--[[
  /* Compare two specified columns between relations.
 * Match col1 in relation r1 with col2 in relation r2
 *
 * Input: r1, r2 = relations to compare
 *        col1, col2 = column indices to match
 * Returns: nonnegative number of differences between columns
 */
]]
function M.Relation:match_columns(obj, col1, col2)
  assert(type(obj) == "table" and type(obj.row_count) == "number" and type(obj.bitfield) == "table", "Relation:match_columns: takes a Relation but got: "..tostring(obj))
  assert(self.row_count == obj.row_count, "Relation:match_columns: row_counts must be the same but: "..tostring(self.bit_count).." ~= "..tostring(obj.bit_count))
  assert(type(col1) == "number" and col1 <= self.column_count, "Relation:match_columns: col1 must be non-negative number <= r1.column_count")
  assert(type(col2) == "number" and col2 <= obj.column_count, "Relation:match_columns: col1 must be non-negative number <= r2.column_count")

  return self.bitfield[col1]:column_diff(obj.bitfield[col2])
end

--[[
  /* Compute the weight of a Column function (as col_matches) r1->r2 */
--]]
function M.Relation:weight(obj, col_matches)
  assert(type(obj) == "table" and type(obj.row_count) == "number" and type(obj.column_count) == "number" and type(obj.bitfield) == "table", "Relation:weight: obj must be a Relation but got: "..tostring(obj))
  assert(type(col_matches) == "table" and #col_matches == self.column_count, "Relation:weight: col_matches must be an array of same size as first relation but: "..tostring(self.column_count).." ~= "..tostring(#col_matches))
  local col_used, use_count, diff

  -- clear image of the match in r2
  col_used = {}
  for i = 1, obj.column_count do
    col_used[i] = 0
  end

  -- apply current match
  diff = 0
  for i = 1, self.column_count do
    diff = diff + self:match_columns(obj, i, col_matches[i])
    col_used[col_matches[i]] = 1
  end

  -- count columns in the image
  use_count = 0
  for i = 1, obj.column_count do
    use_count = use_count + col_used[i]
  end

  -- apply penalty for unmatched columns
  diff = diff + (obj.column_count - use_count) * obj.row_count

  return diff
end

--[[
  matches
  -- an iterator that produces matches cols1 -> cols2
     suitable for use in Relation:min_weight

  Inputs:  cols1, cols2 = positive integer
  Outputs: m1,..,m(cols2^cols1) = sequence of unique col_matches

  Each col_match is a table of length cols1 mapping to cols2. The
  entire sequence has all possible such mappings. E.g.,
    for x in matches(2,2) do print(table.unpack(x)) end
  prints all 2^2 = 4 possible matches, one per line:
    1 1
    2 1
    1 2
    2 2
--]]

local function matches(cols1,cols2)
  assert(math.tointeger(cols1) and cols2 > 0, "matches: cols1 must be positive integer but got: "..tostring(cols1))
  assert(math.tointeger(cols2) and cols2 > 0, "matches: cols2 must be positive integer but got: "..tostring(cols2))
  -- initialize running indices and matches
  local col, maxcol = 1, 1
  local matches = {0}
  for i = 2, cols1 do
    matches[i] = 1
  end

  return function ()
    if matches[col] < cols2 then
      matches[col] = matches[col] + 1
      return matches
    else
      repeat
        col = col + 1
      until col > cols1 or matches[col] < cols2
      if col > cols1 then
        return nil
      else
        matches[col] = matches[col] + 1
        for i = 1, (col - 1) do
          matches[i] = 1
        end
        matches[1] = 1
        col = 1
        return matches
      end
    end
  end
end

--[[
  /* Determine the minimum weight r1->r2 */
--]]
function M.Relation:min_weight(obj)
  assert(type(obj) == "table" and type(obj.row_count) == "number" and type(obj.column_count) == "number" and type(obj.bitfield) == "table", "Relation:min_weight: obj must be a Relation but got: "..tostring(obj))
  local wt, min_wt

  -- initialize worst case
  min_wt = obj.column_count * obj.row_count

  -- use the matches generator
  for col_matches in matches(self.column_count, obj.column_count) do
    wt = self:weight(obj, col_matches)
    if wt < min_wt then min_wt = wt end
  end
  return min_wt
end

--[[
  /* Compute the distance between two relations */
  Inputs:  self, r2 = Relations
  Outputs: relation distance
--]]
function M.Relation:relmetric(r2)
  assert(type(r2) == "table" and type(r2.column_count) == "number", "Relation:relmetric: takes a Column but got: "..tostring(r2))
  local w1, w2
  if M.CHK_WT_BOTH_DIRS then
    w1 = self:min_weight(r2)
    w2 = r2:min_weight(self)
    if w1 > w2 then
      return w1
    else
      return w2
    end
  elseif self.column_count <= r2.column_count then
    return self:min_weight(r2)
  else
    return r2:min_weight(self)
  end
end

--[[
  export the module
--]]
return M
