#! /usr/bin/env lua

--[[
  rel_test
--]]

local RM = require("relmetric")

local c0, c1, c2, c3, c4, c5
c0 = RM.Column:new()
c1 = RM.Column:new({row_count = 32, 0x3000, 0x000f})
c2 = RM.Column:new({row_count = 32, 0x0000, 0x0000})
c3 = RM.Column:new({row_count = 32, 0x100f, 0x0f3f})
c4 = RM.Column:new({row_count = 32, 0x0000, 0x000f})
c5 = RM.Column:new({row_count = 32, 0x0000, 0x0010})

local r0, r1, r2
r0 = RM.Relation:new()
r1 = RM.Relation:new({
  row_count = 32,
  {row_count = 32, 0x3000, 0x000f},
  {row_count = 32, 0x0000, 0x0000}
})
r2 = RM.Relation:new({
  row_count = 32,
  {row_count = 32, 0x100f, 0x0f3f},
  {row_count = 32, 0x0000, 0x000f},
  {row_count = 32, 0x0000, 0x0010}
})
if not (c0:isempty()) then warn("Column 0 is NOT empty") end
if not (r0:isempty()) then warn("Relation 0 is NOT empty") end
if not (r0 == RM.Relation:new()) then warn("Empty Relation 0 NOT == new()") end
if not (r0 == RM.Relation:new({})) then warn("Empty Relation 0 NOT == new({})") end
if not (r0 == RM.Relation:fromints({})) then warn("Empty Relation 0 NOT == fromints({})") end
print(string.format("Relation 1:\n%s", r1))
if not (r1[1] == c1) then warn("Relation 1[1] NOT == Column 1") end
if not (r1[2] == c0) then warn(" Relation 1[2] NOT == Empty Column 0") end
if not (r1[1] == RM.Relation:fromcols(c1, c2)) then warn("Relation 1 NOT == fromcols(c1, c2)") end
print(string.format("Relation 2:\n%s", r2))
print(string.format("Metric = %s", r1:relmetric(r2)))
-- print(string.format("Kappa = %s", r1:kappa(r2)))
if not (c0 < c1) then warn("Empty Column 0 NOT < Column 1") end
if not (c0 >= c1) then warn("Empty Column 0 NOT >= Column 1") end
if not (c1 > c2) then warn("Column 1 NOT > Empty Column 2") end
if not (c2 <= c1) then warn("Empty Column 2 NOT <= Column 1") end
if not (c1 & c0 == c0) then warn("Column 1 & Empty Column 0 NOT == Column 0") end
if not (c1 | c0 == c1) then warn("Column 1 | Empty Column 0 NOT == Column 1") end
if not (c1:column_diff() == 5) then warn("Column 1 <column_diff> nil NOT == 5") end
if not (c1:column_diff({}) == 5) then warn("Column 1 <column_diff> {} NOT == 5") end
if not (c1:column_diff(c0) == 5) then warn("Column 1 <column_diff> Empty Column 0 NOT == 5") end
if not (c0:column_diff(c1) == 5) then warn("Empty Column 0 <column_diff> Column 1 NOT == 5") end
if c0:share_rel(c1) then warn("Empty Column 0 <share_rel> Column 1 is NOT false") end
if not (c1:share_rel(c3)) then warn("Column 1 <share_rel> Column 3 is NOT true") end
if not (r1[1]:share_rel(r2[1])) then warn("Relation 1[1] <share_rel> Relation 2[1] is NOT true") end
-- print(string.format("Any joint rows by column: %s, %s, %s", r1[1]:share_rel(r2[1]), r1[2]:share_rel(r2[2]), r1[3]:share_rel(r2[3])))
