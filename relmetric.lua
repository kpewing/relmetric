--[[
      Lua implementation of relmetric
--]]

-- set up as a module
local M = {}

-- ENVIRONMENT VARIABLE: CHK_WT_BOTH_DIRS
-- whether to check min weight in both directions or rely on Property 2 that
--   if #Y1<=#Y2, then distance(R1,R2) = min weight(g|Y1-Y2))
M.CHK_WT_BOTH_DIRS = (os.getenv("RELMETRIC_CHK_WT_BOTH_DIRS") == "true") or false

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

  M.MAX_INT = math.tointeger(os.getenv("RELMETRIC_MAX_INT")) or 0xffff -- unsigned short
  M.INT_SIZE = 4 * #string.format('%X', M.MAX_INT)
  local HEX_FORM = "0x%0"..tostring(#string.format('%X', M.MAX_INT)).."x"
  M.ROWS_PER_UNSIGNED = M.INT_SIZE
  local ROW_MASK = {}
  ROW_MASK[M.ROWS_PER_UNSIGNED] = 0x1
  for i = M.ROWS_PER_UNSIGNED, 2, -1 do
    ROW_MASK[i - 1] = ROW_MASK[i] << 1
  end

--[[
  /* Column creation and methods */
--]]

-- Default Column is empty with row_count == 0
M.Column = {row_count = 0}

-- new creates a new Column with fields row_count, bits
-- Input: nil or table = {row_count, ...<integer>...}
--        row_count = non-negative count of rows (bits) in the Column
--        <integers> = zero or more integers in big-endian order
--        each bit of which represents one element of the relation
-- Output: Column

function M.Column:new(obj)
  local newObj = {row_count = M.Column.row_count}
  if M.Column.isempty(obj) then
    if obj then
      newObj = {row_count = obj.row_count or M.Column.row_count}
    end
    local int_count = newObj.row_count // M.ROWS_PER_UNSIGNED
    if newObj.row_count % M.ROWS_PER_UNSIGNED > 0 then
      int_count = int_count + 1
    end
    for i = 1, int_count do
      newObj[i] = 0
    end
  else
    assert(type(obj) == "table", "Column:new: takes {row_count,...<integer>...} or {} or nothing but got: "..tostring(obj))
    assert(math.tointeger(obj.row_count) and obj.row_count >= 0, "Column:new: row_count must be a non-negative integer but got: "..tostring(obj.row_count))
    newObj.row_count = obj.row_count
    for i,o in ipairs(obj) do
      assert(math.tointeger(o) and math.tointeger(o) <= M.MAX_INT, string.format("Column:new: takes integers < %s but got: %s", M.MAX_INT, tostring(o)))
      newObj[i] = o
    end
    local bit_count = M.ROWS_PER_UNSIGNED * #newObj
    assert(newObj.row_count <= bit_count, "Column:new: too few bits for row_count: "..tostring(bit_count).." > "..tostring(newObj.row_count))
  end
  self.__index = self
  return setmetatable(newObj, self)
end

-- Column.isempty tests whether an object is an empty Column
-- NOTE:  Empty Columns are a class: for them row_count is arbitrary.
-- Also, nil, {}, and list of 0s are also an empty Column.
function M.Column.isempty(obj)
  local res
  if type(obj) == "nil" then
    -- nil is empty
    res = true
  elseif type(obj) == "table" then
    -- table with a row_count >= 0 and at most 0's
    res = true
    for k,v in pairs(obj) do
      if k == "row_count" and v >= 0 then
        res = true
      elseif math.tointeger(k) and v == 0  then
        res = true
      else
        res = false
        break
      end
    end
  else
    -- must be a table
    res = false
  end
  return res
end

-- fromints creates a Column from integers (2 bytes), inferring the row_count
-- Input (vararg):  table of integers or unpacked table thereof
-- Output:  Column of the input integers with inferred row_count
function M.Column:fromints(...)
  local input = {...}
  -- handle ints enclosed in a table
  if #input == 1 and type(input[1]) == "table" then
    input = input[1]
  end
  input.row_count = M.ROWS_PER_UNSIGNED * #input
  return M.Column:new(input)
end

-- toints converts a Column into integers (2 bytes)
function M.Column:toints()
  local res = {}
  if self:isempty() and self.row_count > 0 then
    local int_count = self.row_count // M.ROWS_PER_UNSIGNED
    if self.row_count % M.ROWS_PER_UNSIGNED > 0 then
      int_count = int_count + 1
    end
    for i = 1, int_count do
      res[i] = 0
    end
    return table.unpack(res)
  else
    return table.unpack(self)
  end
end

-- returns string representation of Column as list of hex ints
function M.Column:tohex()
  return string.format("{"..string.rep(HEX_FORM,#self,', ').."}",table.unpack(self))
end

-- generate a string that prints vertically, most-to-least significant
function M.Column:__tostring()
  local res = ""
  -- if not self:isempty() then
    local whole_ints = self.row_count // M.ROWS_PER_UNSIGNED
    local rest_bits = self.row_count % M.ROWS_PER_UNSIGNED
    local ints = {self:toints()}
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
    -- now the rest, ignoring if rest_bits == 0
    for j = (M.ROWS_PER_UNSIGNED - rest_bits + 1), M.ROWS_PER_UNSIGNED do
      if ints[whole_ints + 1] & ROW_MASK[j] > 0 then
        res = res..string.format("%s\n",'1')
      else
        res = res..string.format("%s\n",'0')
      end
    end
    -- res = res..string.format("\n")
  -- elseif self.row_count > 0 then
  --   local int_count = self.row_count // M.ROWS_PER_UNSIGNED
  --   if self.row_count % M.ROWS_PER_UNSIGNED > 0 then
  --     int_count = int_count + 1
  --   end
  --   res = string.rep("0\n", int_count)
  -- end
  return res
end

-- equality of Columns
function M.Column:__eq(obj)
  assert(type(obj) == "table" and math.tointeger(obj.row_count), "Column:__eq takes Columns but got: "..tostring(obj))
  local res
  local self_empty = self:isempty()
  local obj_empty = M.Column.isempty(obj)

  if self_empty and obj_empty then
    res = true
  elseif self_empty or obj_empty then
    res = false
  else
    if self.row_count ~= obj.row_count then
      res = false
    else
      local ints1 = {self:toints()}
      local ints2 = {obj:toints()}
      if #ints1 ~= #ints2 then
        res = false
      else
        res = true
        for i = 1, #ints1 do
          if ints1[i] ~= ints2[i] then
            res = false
          end
        end
      end
    end
  end
  return res
end

-- less than or equal for Columns
function M.Column:__le(obj)
  assert(type(obj) == "table" and math.tointeger(obj.row_count), "Column:__le takes Columns but got: "..tostring(obj))
  local res

  if self:isempty() then
    res = true
  elseif M.Column.isempty(obj) then
    res = false
  else
    local ints1 = {self:toints()}
    local ints2 = {obj:toints()}
    assert(self.row_count == obj.row_count or #ints1 == 0 or #ints2 == 0, "Column:__le requires non-empty Columns to have equal row_count but: "..tostring(obj.row_count).." ~= "..tostring(self.row_count))
    assert(#ints1 == #ints2 or #ints1 == 0 or #ints2 == 0, "Column:__le requires non-empty Columns to have equal length but: "..tostring(#ints1).." ~= "..tostring(#ints2))
    res = true
    for i = 1, #ints1 do
      if ints1[i] > ints2[i] then
        res = false
        break
      elseif ints1[i] < ints2[i] then
        res = true
        break
      end
    end
  end
  return res
end

-- less than for Columns
function M.Column:__lt(obj)
  assert(type(obj) == "table" and math.tointeger(obj.row_count), "Column:__lt takes Columns but got: "..tostring(obj))
  local res

  if M.Column.isempty(obj) then
    res = false
  elseif M.Column.isempty(self) then
    res = true
  else
    local ints1 = {self:toints()}
    local ints2 = {obj:toints()}
    assert(self.row_count == obj.row_count or #ints1 == 0 or #ints2 == 0, "Column:__lt requires non-empty Columns to have equal row_count but: "..tostring(obj.row_count).." ~= "..tostring(self.row_count))
    assert(#ints1 == #ints2 or #ints1 == 0 or #ints2 == 0, "Column:__lt requires non-empty Columns to have equal length but: "..tostring(#ints1).." ~= "..tostring(#ints2))
    res = false
    for i = 1, #ints1 do
      if ints1[i] > ints2[i] then
        res = false
        break
      elseif ints1[i] < ints2[i] then
        res = true
        break
      end
    end
  end
  return res
end

-- __band for Columns
function M.Column:__band(obj)
  assert(type(obj) == "table" and math.tointeger(obj.row_count), "Column:__band takes Columns but got: "..tostring(obj))
  local res = true

  if M.Column.isempty(obj) then
    res = M.Column:new(self)
  elseif self:isempty() then
    res = M.Column:new(obj)
  else
    local ints1 = {self:toints()}
    local ints2 = {obj:toints()}
    assert(self.row_count == obj.row_count or #ints1 == 0 or #ints2 == 0, "Column:__band requires non-empty Columns to have equal or 0 row_count but: "..tostring(obj.row_count).." ~= "..tostring(self.row_count))
    assert(#ints1 == #ints2 or #ints1 == 0 or #ints2 == 0, "Column:__band requires non-empty Columns to have equal or 0 length but: "..tostring(#ints1).." ~= "..tostring(#ints2))
    local new_ints, new_row_count = {}, 0
    if #ints1 == 0 then
      for i = 1, #ints2 do
        new_ints[i] = 0x0
        new_row_count = obj.row_count
      end
    elseif #ints2 == 0 then
      for i = 1, #ints1 do
        new_ints[i] = 0x0
        new_row_count = self.row_count
      end
    else
      for i = 1, #ints1 do
        new_ints[i] = ints1[i] & ints2[i]
        new_row_count = self.row_count
      end
    end
    res = M.Column:fromints(new_ints)
    res.row_count = new_row_count
  end
  return res
end

-- __bor for Columns
function M.Column:__bor(obj)
  assert(type(obj) == "table" and math.tointeger(obj.row_count), "Column:__bor takes Columns but got: "..tostring(obj))
  local res

  if M.Column.isempty(obj) then
    res = M.Column:new(self)
  elseif self:isempty() then
    res = M.Column:new(obj)
  else
    local ints1 = {self:toints()}
    local ints2 = {obj:toints()}
    assert(self.row_count == obj.row_count or #ints1 == 0 or #ints2 == 0, "Column:__bor requires non-empty Columns to have equal row_count but: "..tostring(obj.row_count).." ~= "..tostring(self.row_count))
    assert(#ints1 == #ints2 or #ints1 == 0 or #ints2 == 0, "Column:__bor requires non-empty Columns to have equal length but: "..tostring(#ints1).." ~= "..tostring(#ints2))
    local new_ints, new_row_count = {}, 0
    if #ints1 == 0 then
      for i = 1, #ints2 do
        new_ints[i] = ints2[i]
        new_row_count = obj.row_count
      end
    elseif #ints2 == 0 then
      for i = 1, #ints1 do
        new_ints[i] = ints1[i]
        new_row_count = self.row_count
      end
    else
      for i = 1, #ints1 do
        new_ints[i] = ints1[i] | ints2[i]
        new_row_count = self.row_count
      end
    end
    res = M.Column:fromints(new_ints)
    res.row_count = new_row_count
    return res
  end
end

-- isdisjoint checks whether two Columns are disjoint by rows
-- Input:  obj = a Column
-- Output: boolean whether input and self are disjoint by rows
function M.Column:isdisjoint(obj)
  local res
  if self:isempty() and M.Column.isempty(obj) then
    res = true
  elseif not self:isempty() and not M.Column.isempty(obj) then
    assert(type(obj) == "table" and math.tointeger(obj.row_count), "Column:isdisjoint: takes Columns but got: "..tostring(obj))
    local ints1 = {self:toints()}
    local ints2 = {obj:toints()}
    assert(self.row_count == obj.row_count, "Column:isdisjoint: requires non-empty Columns to have equal row_count but: "..tostring(obj.row_count).." ~= "..tostring(self.row_count))
    assert(#ints1 == #ints2, "Column:isdisjoint: requires non-empty Columns to have equal length but: "..tostring(#ints1).." ~= "..tostring(#ints2))

    for i, x in ipairs(ints1) do
      if (x & ints2[i] > 0) then
        res = false
        break
      end
    end
  else
    res = true
  end
  return res
end

--[[
 /* Count the number of differences between two columns
 * Input: second column to which self is to be compared
 * Returns: difference count
   NOTE: empty Column is category initial, i.e., all 0,
   so column_diff with an empty Column counts 1s in other.
 */
--]]
function M.Column:column_diff(obj)
  local diff, ints1, ints2 = 0, {}, {}
  local self_empty = self:isempty()
  local obj_empty = M.Column.isempty(obj)

  if self_empty then
    for i = 1, #ints2 do
      ints1[i] = 0
    end
    ints2 = {obj:toints()}
  elseif obj_empty then
    ints1 = {self:toints()}
    for i = 1, #ints1 do
      ints2[i] = 0
    end
  else
    assert(type(obj) == "table" and math.tointeger(obj.row_count), "Column:column_diff: takes a Column but got: "..tostring(obj))
    assert(self.row_count == obj.row_count, "Column:column_diff requires non-empty Columns to have equal row_count but: "..tostring(obj.row_count).." ~= "..tostring(self.row_count))
    assert(#ints1 == #ints2, "Column:column_diff requires non-empty Columns to have equal length but: "..tostring(#ints1).." ~= "..tostring(#ints2))
    ints1 = {self:toints()}
    ints2 = {obj:toints()}
  end
  if #ints1 > 0 then
    local current_diff, whole_ints, rest_bits
    whole_ints = self.row_count // M.ROWS_PER_UNSIGNED
    rest_bits = self.row_count % 8

    -- unpack whole words
    for i = 1, whole_ints do
      current_diff = ints1[i] ~ ints2[i]
      for j = 1, M.ROWS_PER_UNSIGNED do
        diff = diff + (current_diff & 0x01)
        current_diff = current_diff >> 1
      end
    end

    -- collect remaining rows
    if rest_bits > 0 then
      current_diff = ints1[#ints1] ~ ints2[#ints2]
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

-- Default Relation is empty with row_count == 0
M.Relation = {row_count = 0}

-- new creates a new Relation with field row_count and Columns
-- Input: nil or table  = {row_count, ...<Columns>...}
--        row_count = non-negative count of rows (bits) in all Columns
--        <Columns> = zero or more Columns
-- Output: Relation

function M.Relation:new(obj)
  local newObj = {row_count = M.Relation.row_count}
  if M.Relation.isempty(obj) then
    if obj then
      newObj = {row_count = obj.row_count or M.Relation.row_count}
    end
    if newObj.row_count > 0 then
      newObj[1] = M.Column:new({row_count = newObj.row_count})
    end
  else
    assert(type(obj) == "table", "Relation:new: takes {row_count,...<Column>...} or {} or nothing but got: "..tostring(obj))
    assert(math.tointeger(obj.row_count) and obj.row_count >= 0, "Relation:new: row_count must be a non-negative integer but got: "..tostring(obj.row_count))
    local col_int_count, empty_cols, bit_count = nil, {}, nil

    newObj.row_count = obj.row_count
    for i,o in ipairs(obj) do
      assert(type(o) == "table", "Relation:new: takes Columns but got: "..tostring(o))
      if M.Column.isempty(o) then
        empty_cols[#empty_cols+1] = i
      else
        if not col_int_count then
          col_int_count = #o
          bit_count = M.ROWS_PER_UNSIGNED * col_int_count
          assert(newObj.row_count <= bit_count, "Relation:new: too few bits for row_count: "..tostring(bit_count).." > "..tostring(newObj.row_count))
        else
          assert(o.row_count == newObj.row_count, "Relation:new: all non-empty Columns must have same row_count but: "..tostring(o.row_count).." ~= "..tostring(newObj.row_count))
          assert(#o == col_int_count, "Relation:new: all non-empty Columns must have the same bit length but: "..tostring(#o * M.ROWS_PER_UNSIGNED).." ~= "..tostring(col_int_count * M.ROWS_PER_UNSIGNED))
        end
      end
      newObj[i] = M.Column:new(o)
    end
    for _, col in ipairs(empty_cols) do
      newObj[col] = M.Column:new({row_count = newObj.row_count})
    end
  end
  self.__index = self
  return setmetatable(newObj, self)
end

-- Relation.isempty tests whether an object is an empty Relation
-- NOTE:  Empty Relations are a class: for them row_count is arbitrary.
-- Also, nil, {}, and a list of empty Columns are also an empty Relation.
function M.Relation.isempty(obj)
  local res
  if type(obj) == "nil" then
    -- nil is empty
    res = true
  elseif type(obj) == "table" then
    -- table with a row_count key and empty columns
    res = true
    for k,v in pairs(obj) do
      if k == "row_count" and v >= 0 then
        res = true
      elseif math.tointeger(k) and M.Column.isempty(v) then
        res = true
      else
        res = false
        break
      end
    end
  else
    -- must be a table
    res = false
  end
  return res
end

-- fromcols creates a relation from Columns, inferring the row_count
-- Inputs (vararg) = table of Columns or unpacked table thereof
-- Output: Relation of the input Columns with row_count == #col1_row_count
function M.Relation:fromcols(...)
  local input = {...}
  -- handle cols enclosed in a table
  if #input == 1 and type(input[1]) == "table" and not input[1].row_count then
    input = input[1]
  end
  if M.Relation.isempty(input) then
    input.row_count = M.Relation.row_count
  else
    assert(type(input[1]) == "table" and math.tointeger(input[1].row_count), "Relation:fromcols takes Columns or a (maybe empty) list of them but got: "..tostring(input[1]))
    input.row_count = input[1].row_count
  end
  return M.Relation:new(input)  -- for convience fromcols({}) == new()
end

-- tocols returns the Columns of a Relation
function M.Relation:tocols()
  return table.unpack(self)
end

-- fromints creates a relation from tables of integers representing columns
-- Inputs (vararg): table or unpacked table of tables of integers
-- Output: Relation of the input Columns with row_count inferred
function M.Relation:fromints(...)
  local input = {...}
  local new_rel = {}
  -- handle ints enclosed in a table
  if #input == 1 and type(input[1]) == "table" and type(input[1][1]) == "table" then
    input = input[1]
  end
  if M.Relation.isempty(input) then
    new_rel.row_count = M.Relation.row_count
  else
    assert(type(input[1]) == "table", "Relation:fromints: takes tables of integers but got: "..tostring(input[1]))
    local col_int_count, empty_cols = nil, {}
    for i, o in ipairs(input) do
      assert(type(o) == "table", "Relation:fromints: takes tables of integers but got: "..tostring(o))
      if M.Column.isempty(o) then
        empty_cols[#empty_cols+1] = i
      else
        if not col_int_count then
          col_int_count = #o
        else
          assert(#o == col_int_count, "Relation:fromints: all non-empty Columns must have the same bit length but got: "..tostring(#o * M.ROWS_PER_UNSIGNED).." ~= "..tostring(col_int_count * M.ROWS_PER_UNSIGNED))
        end
      end
      new_rel[i] = M.Column:fromints(o)
    end
    new_rel.row_count = col_int_count * M.ROWS_PER_UNSIGNED
    for _, col in ipairs(empty_cols) do
      new_rel[col] = M.Column:new({row_count = new_rel.row_count})
    end
  end
  return M.Relation:new(new_rel)
end

-- toints returns the tables of integers representing columns
function M.Relation:toints()
  local res = {}
  for i, c in ipairs(self) do
    res[i] = {c:toints()}
  end
  return table.unpack(res)
end

-- tohex returns string representation of Relation as lists of hex ints
function M.Relation:tohex()
  local s = ""
  for i,c in ipairs(self) do
    s = s..string.format("Col %s: %s\n",i, c:tohex())
  end
  return s
end

-- generate a string that prints out a relation
function M.Relation:__tostring()
  local res = ""
  if not self:isempty() then
    local whole_ints = self.row_count // M.ROWS_PER_UNSIGNED
    local rest_bits = self.row_count % 8
    local cols = {self:toints()}
    -- first the whole bytes
    for i = 1, whole_ints do
      for j = 1, #ROW_MASK do
        for k = 1, #self do
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
      for k = 1, #self do
        if cols[k][whole_ints + 1] & ROW_MASK[j] > 0 then
          res = res..string.format("%s",'1')
        else
          res = res..string.format("%s",'0')
        end
      end
      res = res..string.format("\n")
    end
  end
  return res
end

-- __sub one-for-one removes identical columns from self found in input
-- Input:  obj = a Relation
-- Output: self - obj = a new Relation
function M.Relation:__sub(obj)
  local new_rel = {}
  if M.Relation.isempty(obj) then
    new_rel = self
  elseif not self:isempty() then
    assert(type(obj) == "table", "Relation:__sub: takes a Relation but got: "..tostring(obj))
    assert(self.row_count == obj.row_count, "Relation:__sub: requires non-empty Relations to have equal row_counts but: "..tostring(self.row_count).." ~= "..tostring(obj.row_count))
    new_rel.row_count = self.row_count
    local used_cols = {}
    for _, self_col in ipairs(self) do
      for j, obj_col in ipairs(obj) do
        if not used_cols[j] and self_col == obj_col then
          used_cols[j] = true
          break
        else
          new_rel[#new_rel+1] = self_col
        end
      end
    end
  end
  return M.Relation:new(new_rel)
end

-- function M.merge_sort(cols)
--   local left, right = {}, {}
--   if #cols <= 1 then
--     return cols
--   else
--     local mid = #cols // 2 + 1
--     for i, x in ipairs(cols) do
--       if i < mid then
--         left[#left+1] = x
--       else
--         right[#right+1] = x
--       end
--     end
--     left = M.merge_sort(left)
--     right = M.merge_sort(right)
--   end
--   return M.merge(left, right)
-- end

-- function M.merge(left,right)
--   local res = {}
--   while #left > 0 and #right > 0 do
--     if left[1] <= right[1] then
--       res[#res+1] = left[1]
--       table.remove(left, 1)
--     else
--       res[#res+1] = right[1]
--       table.remove(right, 1)
--     end
--   end
--   while #left > 0 do
--     res[#res+1] = left[1]
--     table.remove(left, 1)
--   end
--   while #right > 0 do
--     res[#res+1] = right[1]
--     table.remove(right, 1)
--   end
--   return res
-- end

-- sorted returns a new Relation == self lexically sorted
function M.Relation:sorted()
  local res = M.Relation:new(self)
  if not self:isempty() then
    table.sort(res)
  end
  return res
end

-- xgroup partitions a Relation by intersection of rows
-- Input:  obj = {} or nil or non-empty Column
-- Output: list of X-groups = {<X-group>, ...}
--   Each X-group = {max = <Colum>, ...<integer>...} where
--   each <integer> is an index in self to a Column and
--   the max is a Column that is the union of all these Columns.
function M.Relation:xgroup(obj)
  local res, zero_group = {}, {max = M.Column:new({row_count = self.row_count})}
  local col_used = {}
  -- construct the X-groups
  if not self:isempty() then
    -- quickly handle initial empties
    local start_i = 1
    while self[start_i] == zero_group.max do
      zero_group[#zero_group + 1] = start_i
      start_i = start_i + 1
    end
    if #zero_group > 0 then res[1] = zero_group end
    -- loop over remaining columns
    res[start_i] = {max = self[start_i]}
    for i = start_i, #self do
      local col = self[i]
      local isdisjnt = nil
      -- check col v. all groups
      for j, grp in ipairs(res) do
        local expanded = nil
        if not expanded then
          -- haven't yet found an overlapping grp j to expand: this grp?
          isdisjnt = grp.max:isdisjoint(col)
          if not isdisjnt then
            grp[#grp + 1] = i
            grp.max = (grp.max | col)
            expanded = j
            break
          end
        else
          -- col overlapped grp expanded: combine with any remaining grps?
          isdisjnt = res[expanded].max:isdisjoint(grp)
          if not isdisjnt then
            table.move(grp, 1, #grp, #res[expanded]+1, res[expanded])
            res[expanded].max = (res[expanded].max | grp.max)
          end
        end
      end
      -- create a new group for col if disjoint from all grps
      if isdisjnt then
        res[#res+1] = {max = col, i}
      end
    end

    -- restrict to the xgroup matching obj
    if obj then
      assert(type(obj) == "table" and math.tointeger(obj.row_count) and math.tointeger(obj[1]), "Relation:xgroup: takes a Column but got: "..tostring(obj))
      -- find and return just the xgroup intersecting obj
      for _, xg in ipairs(res) do
        if xg.max & obj then
          res = xg
          break
        end
      end
    end
  end
  return res
end

-- kappa returns the `kappa' value for a Relation according to the algorithm in
-- Kenneth P. Ewing, ``Bounds for the Distance Between Relations'', arXiv:2105.01690.
function M.Relation:kappa(...)
  local res
  local max_count = math.tointeger(...)
  assert(not ... or (max_count and max_count >= 0), "Relation:kappa: optional max_count must be non-negative integer but got: "..tostring(...))
  if self:isempty() then
    return 0
  else
    local blockcounts = {}
    local xgs = self:xgroup()
    for i, g in ipairs(xgs) do
      blockcounts[#blockcounts+1] = #g
    end
    table.sort(blockcounts)
    local blocksums = {}
    blocksums[1] = blockcounts[1]
    for i = 2, #blockcounts do
      blocksums[i] = blocksums[i-1] + blockcounts[i]
    end
    local cap = max_count or #self
    local m = 0
    if blocksums[1] <= cap then
      repeat
        m = m + 1
      until m > #blocksums or blocksums[m] > cap
    end
    if #blocksums == 1 then
      res = 0
    elseif cap >= #self then
      res = blocksums[m-1]
    elseif blocksums[m] + blockcounts[m] > cap then
      res = blocksums[m-1]
    else
      res = blocksums[m]
    end
  end
  return res
end

-- rel_dist_bound returns the bound on the Relation metric in
-- Kenneth P. Ewing, ``Bounds for the Distance Between Relations'', arXiv:2105.01690.
function M.Relation:rel_dist_bound(obj)
  assert(type(obj) == "table", "Relation:rel_dist_bound: takes a Relation but got: "..tostring(obj))
  local res
  local delta12, delta21 = self - obj, obj - self
  local kappa12, kappa21 = self:kappa(#obj), obj:kappa(#self)
  res = math.max(#self, #obj) - math.min(#self - #delta12 + kappa12, #obj - #delta21 + kappa21)
  return res
end


--[[
  /* Compare two specified columns between relations.
 * Match col1 in relation r1 with col2 in relation r2
 *
 * Input: self, obj = relations to compare
 *        col1, col2 = column indices to match
 * Returns: nonnegative number of differences between columns
   NOTE: Empty Column is category initial, i.e., all 0,
   so match_column with an empty Column counts 1s in other.
 */
]]
function M.Relation:match_columns(obj, col1, col2)
  assert(type(obj) == "table", "Relation:match_columns: takes a Relation but got: "..tostring(obj))
  local self_empty = self:isempty()
  local obj_empty = M.Relation.isempty(obj)
  assert(self_empty or (math.tointeger(col1) and col1 > 0 and col1 <= #self), "Relation:match_columns: col1 out of range: "..tostring(col1))
  assert(obj_empty or (math.tointeger(col2) and col2 > 0 and col2 <= #obj), "Relation:match_columns: col2 out of range: "..tostring(col2))

  local diff
  if self_empty and obj_empty then
    diff = 0
  elseif self_empty then
    diff = obj[col2]:column_diff(self)
  elseif obj_empty then
    diff = self[col1]:column_diff(obj)
  else
    diff = self[col1]:column_diff(obj[col2])
  end
  return diff
end

--[[
  /* Compute the weight of a Column function as col_matches : self -> obj */
    NOTE: Weight between empty Relations is 0. Weight to an empty
    Relation simply counts the 1s in the other and from an empty Relation
    counts Columns and the 1s in the other.
--]]
function M.Relation:weight(obj, col_matches)
  assert(type(obj) == "table", "Relation:weight: takes a Relation but got: "..tostring(obj))
  assert(type(col_matches) == "table" and #col_matches == #self, "Relation:weight: col_matches must be an array of same size as source Relation but: "..tostring(#self).." ~= "..tostring(#col_matches))
  local from_col_count, to_col_count = 0, 0
  local diff, col_used, use_count

  -- handle empty Relations
  local self_empty = self:isempty()
  local obj_empty = M.Relation.isempty(obj)
  if self_empty and obj_empty then
    -- g: Rel_0 -> Rel_0
    from_col_count = 0
    to_col_count = 0
  elseif self_empty then
    -- g: Rel_0 -> obj
    from_col_count = #obj
    to_col_count = #obj
  elseif obj_empty then
    -- g: self -> Rel_0
    from_col_count = #self
    to_col_count = #self
  else
    from_col_count = #self
    to_col_count = #obj
  end

  -- clear image of the match in obj
  col_used = {}
  for i = 1, to_col_count do
    col_used[i] = 0
  end

  -- apply current match
  diff = 0
  for i = 1, from_col_count do
    diff = diff + self:match_columns(obj, i, col_matches[i])
    col_used[col_matches[i]] = 1
  end

  -- count columns in the image
  use_count = 0
  -- leave 0 when self is empty (Rel_0)
  if not self_empty then
    for i = 1, to_col_count do
      use_count = use_count + col_used[i]
    end
  end

  -- apply penalty for unmatched columns
  diff = diff + (to_col_count - use_count)

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

-- function M.matches(cols1,cols2)
local function matches(cols1,cols2)
  assert(math.tointeger(cols1) and cols2 >= 0, "matches: cols1 must be positive integer but got: "..tostring(cols1))
  assert(math.tointeger(cols2) and cols2 >= 0, "matches: cols2 must be positive integer but got: "..tostring(cols2))
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
  /* Determine the minimum weight self -> obj */
--]]
function M.Relation:min_weight(obj)
  -- assert(not M.Relation.isempty(self), "Relation:min_weight: self must be a non-empty Relation but have: "..tostring(obj))
  -- assert(not M.Relation.isempty(obj), "Relation:min_weight: obj must be a non-empty Relation but got: "..tostring(obj))
  -- assert(#self.bitfield > 0, "Relation:min_weight: self must be a non-empty Relation")
  -- assert(type(obj.bitfield) == "table" and #obj.bitfield > 0, "Relation:min_weight: obj must be a non-empty Relation but got: "..tostring(obj))
  -- assert(math.tointeger(obj.row_count) and math.tointeger(obj.column_count), "Relation:min_weight: obj must be a Relation but got: "..tostring(obj))
  local wt, min_wt

  -- handle empty Relations
  local from_col_count, to_col_count = 0, 0
  if not self:isempty() then from_col_count = #self end
  if not M.Relation.isempty(obj) then to_col_count = #obj end

  -- initialize worst case
  -- min_wt = obj.column_count * obj.row_count
  min_wt = to_col_count * (obj.row_count or 0)

  -- use the matches generator
  for col_matches in matches(from_col_count, to_col_count) do
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
  assert(type(r2) == "table", "Relation:relmetric: takes a Column but got: "..tostring(r2))
  local w1, w2
  if M.CHK_WT_BOTH_DIRS then
    w1 = self:min_weight(r2)
    w2 = r2:min_weight(self)
    if w1 > w2 then
      return w1
    else
      return w2
    end
  else
    -- handle empty Relations
    local from_col_count, to_col_count = 0, 0
    if not self:isempty() then from_col_count = #self end
    if not M.Relation.isempty(r2) then to_col_count = #r2 end

    if from_col_count <= to_col_count then
      return self:min_weight(r2)
    else
      return r2:min_weight(self)
    end
  end
end

--[[
  export the module
--]]
return M
