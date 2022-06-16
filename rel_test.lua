#! /usr/bin/env lua

--[[
  rel_test
--]]

local relmetric = require("relmetric")

local c0, c1, c2, c3, c4, c5
c0 = relmetric.Column:new()
c1 = relmetric.Column:new({row_count = 32, 0x3000, 0x000f})
c2 = relmetric.Column:new({row_count = 32, 0x0000, 0x0000})
c3 = relmetric.Column:new({row_count = 32, 0x100f, 0x0f3f})
c4 = relmetric.Column:new({row_count = 32, 0x0000, 0x000f})
c5 = relmetric.Column:new({row_count = 32, 0x0000, 0x0010})

local r0, r1, r2, r3
r0 = relmetric.Relation:new()
r1 = relmetric.Relation:new({
  row_count = 32,
  {row_count = 32, 0x3000, 0x000f},
  {row_count = 32, 0x0000, 0x0000}
})
r2 = relmetric.Relation:new({
  row_count = 32,
  {row_count = 32, 0x100f, 0x0f3f},
  {row_count = 32, 0x0000, 0x000f},
  {row_count = 32, 0x0000, 0x0010}
})
r3 = relmetric.Relation:fromcols(c3, c4, c5)

local R, R4
R = relmetric.Relation:fromints({
  {0x0},
  {0x08},
  {0x0c},
  {0x0c},
  {0x02},
  {0x02},
  {0x01},
  {0x01},
  {0x01},
  {0x01}
})
R4 = relmetric.Relation:fromints({
  {0x0b, 0x80},
  {0x07, 0x80},
  {0x0b, 0x80},
  {0x0c, 0x80},
  {0x03, 0x80},
  {0x00, 0x00},
  {0x08, 0x80},
  {0x0c, 0x80},
  {0x08, 0x80},
  {0x0d, 0x80}
})


if not (c0:isempty()) then warn("Column 0 is NOT empty") end
if not (c0 < c1) then warn("Empty Column 0 NOT < Column 1") end
if not (c0 >= c1) then warn("Empty Column 0 NOT >= Column 1") end
if not (c1 > c2) then warn("Column 1 NOT > Empty Column 2") end
if not (c1 < c3) then warn("Column 1 NOT < Column 3") end
if not (c2 <= c1) then warn("Empty Column 2 NOT <= Column 1") end
if not (c1 & c0 == c0) then warn("Column 1 & Empty Column 0 NOT == Column 0") end
if not (c1 | c0 == c1) then warn("Column 1 | Empty Column 0 NOT == Column 1") end
if not (c1:column_diff() == 5) then warn("Column 1 <column_diff> nil NOT == 5") end
if not (c1:column_diff({}) == 5) then warn("Column 1 <column_diff> {} NOT == 5") end
if not (c1:column_diff(c0) == 5) then warn("Column 1 <column_diff> Empty Column 0 NOT == 5") end
if not (c0:column_diff(c1) == 5) then warn("Empty Column 0 <column_diff> Column 1 NOT == 5") end
if not c0:isdisjoint(c1) then warn("Empty Column 0 <isdisjoint> Column 1 is NOT true") end
if c1:isdisjoint(c3) then warn("Column 1 <isdisjoint> Column 3 is NOT false") end
if not (r0:isempty()) then warn("Relation 0 is NOT empty") end
if not (r0 == relmetric.Relation:new()) then warn("Empty Relation 0 NOT == new()") end
if not (r0 == relmetric.Relation:new({})) then warn("Empty Relation 0 NOT == new({})") end
if not (r0 == relmetric.Relation:fromints({})) then warn("Empty Relation 0 NOT == fromints({})") end
print(string.format("Relation 1:\n%s", r1))
if not (r1[1] == c1) then warn("Relation 1[1] NOT == Column 1") end
if not (r1[2] == c0) then warn(" Relation 1[2] NOT == Empty Column 0") end
if not (r1[1] == relmetric.Relation:fromcols(c1, c2)) then warn("Relation 1 NOT == fromcols(c1, c2)") end
print(string.format("Sorted Relation 1:\n", r1:sorted()))
print(string.format("Relation 2:\n%s", r2))
if r1[1]:isdisjoint(r2[1]) then warn("Relation 1[1] <isdisjoint> Relation 2[1] is NOT false") end
print(string.format("Sorted Relation 2:\n", r2:sorted()))
print(string.format("Metric (Relation 1, Relation 2) = %s", r1:relmetric(r2)))
print(string.format("Relation 3:\n%s", r3))
print(string.format("Relation R:\n%s", R))
print(string.format("Relation R4:\n%s", R4))
