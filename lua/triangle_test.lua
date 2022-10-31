#! /usr/bin/env lua
--[[
  triangle_test
--]]

local RM = require("relmetric")

local rows_per_unsigned =  RM.ROWS_PER_UNSIGNED
local TEST_CASES, MAX_COLS, MAX_ROWS = 10, 6, 8
local r1rows, cols, int_count
local ints, bf, rels = {}, {}, {}
local d12, d13, d23
local fail

for t = 1, TEST_CASES do
  -- randomly size and populate relations
  r1rows = math.random(MAX_ROWS)
  cols = math.random(MAX_COLS)
  int_count = r1rows // rows_per_unsigned + 1
  for r = 1, 3 do
    bf = {}
    for i = 1, cols do
      ints = {}
      for j = 1, int_count do
        ints[j] = math.random(0xFFFF)
      end
      bf[i] = RM.Column:new({row_count = r1rows, table.unpack(ints)})
    end
    rels[r] = RM.Relation:fromcols(bf)
  end

  -- compute distances
  d12 = rels[1]:relmetric(rels[2])
  d13 = rels[1]:relmetric(rels[3])
  d23 = rels[2]:relmetric(rels[3])

  -- test for triangle inequality
  fail = 0
  if d13 > (d12 + d23) then
    print(string.format("Violation 1-3: %d > (%d + %d)", d13, d12, d23))
    fail = 1
  end
  if d12 > (d13 + d23) then
    print(string.format("Violation 1-2: %d > (%d + %d)", d12, d13, d23))
    fail = 2
  end
  if d23 > (d12 + d13) then
    print(string.format("Violation 2-3: %d > (%d + %d)", d23, d12, d13))
    fail = 3
  end
  if fail > 0 then
    print("Relation 1:")
    print(rels[1])
    print("")
    print("Relation 2:")
    print(rels[2])
    print("")
    print("Relation 3:")
    print(rels[3])
    print("")
  else
    print("Pass")
  end
end
