#! /usr/bin/env lua

--[[
  rel_test
--]]

local relmetric = require("relmetric")
local fail = false

local c0, c1, c2, c3, c4, c5
c0 = relmetric.Column:new()
c1 = relmetric.Column:new({row_count = 32, 0x3000, 0x000f})
c2 = relmetric.Column:new({row_count = 32, 0x0000, 0x0000})
c3 = relmetric.Column:new({row_count = 32, 0x100f, 0x0f3f})
c4 = relmetric.Column:new({row_count = 32, 0x0000, 0x000f})
c5 = relmetric.Column:new({row_count = 32, 0x0000, 0x0010})

local r0, r1, r2
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

local R, E4_8, E4_9
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
-- [ ] fix: E4_8 = relmetric.Relation:fromcols({R[2], R[3], R[4], R[5]})
-- [ ] fix: E4_9 = relmetric.Relation:fromcols({R[1], R[2], R[3], R[4], R[5]})
E4_17R1 = relmetric.Relation:fromints({
  {0x0b, 0x08},
  {0x07, 0x08},
  {0x0b, 0x08},
  {0x0c, 0x08},
  {0x03, 0x08},
  {0x00, 0x00},
  {0x08, 0x08},
  {0x0c, 0x08},
  {0x04, 0x08},
  {0x0d, 0x08}
})
E4_17R2 = relmetric.Relation:fromints({
  {0x02, 0x00},
  {0x01, 0x00},
  {0x0e, 0x00},
  {0x0f, 0x00},
  {0x04, 0x00},
  {0x0e, 0x08},
  {0x0a, 0x00},
  {0x0d, 0x00},
  {0x07, 0x08},
  {0x0a, 0x08}
})
E4_18R1 = relmetric.Relation:fromints({
  {0x00, 0x00},
  {0x02, 0x08},
  {0x0c, 0x00},
  {0x02, 0x00},
  {0x04, 0x00},
  {0x08, 0x00},
  {0x02, 0x08},
  {0x00, 0x00},
  {0x02, 0x00},
  {0x0c, 0x00}
})
E4_18R2 = relmetric.Relation:fromints({
  {0x00, 0x00},
  {0x02, 0x08},
  {0x0c, 0x00},
  {0x06, 0x00},
  {0x04, 0x00},
  {0x08, 0x00},
  {0x00, 0x08},
  {0x00, 0x08},
  {0x02, 0x00},
  {0x09, 0x00}
})

-- Test relmetric.Column methods
print("Test relmetric.Column methods")
if not (c0:isempty()) then fail = true; warn("Column 0 is NOT empty") end
if not (c0 < c1) then fail = true; warn("Empty Column 0 NOT < Column 1") end
if not (c0 >= c1) then fail = true; warn("Empty Column 0 NOT >= Column 1") end
if not (c1 > c2) then fail = true; warn("Column 1 NOT > Empty Column 2") end
if not (c1 < c3) then fail = true; warn("Column 1 NOT < Column 3") end
if not (c2 <= c1) then fail = true; warn("Empty Column 2 NOT <= Column 1") end
if not (c1 & c0 == c0) then fail = true; warn("Column 1 & Empty Column 0 NOT == Column 0") end
if not (c1 | c0 == c1) then fail = true; warn("Column 1 | Empty Column 0 NOT == Column 1") end
if not (c1:column_diff() == 5) then fail = true; warn("Column 1 <column_diff> nil NOT == 5") end
if not (c1:column_diff({}) == 5) then fail = true; warn("Column 1 <column_diff> {} NOT == 5") end
if not (c1:column_diff(c0) == 5) then fail = true; warn("Column 1 <column_diff> Empty Column 0 NOT == 5") end
if not (c0:column_diff(c1) == 5) then fail = true; warn("Empty Column 0 <column_diff> Column 1 NOT == 5") end
if not c0:isdisjoint(c1) then fail = true; warn("Empty Column 0 <isdisjoint> Column 1 is NOT true") end
if c1:isdisjoint(c3) then fail = true; warn("Column 1 <isdisjoint> Column 3 is NOT false") end
if fail == true then print("> Column methods: OK\n"); fail = false else print("> Column methods: fails\n\n") end

-- Test relmetric.Relation methods
print("Test relmetric.Relation methods")
if not (r0:isempty()) then fail = true; warn("Relation 0 is NOT empty") end
if not (r0 == relmetric.Relation:new()) then fail = true; warn("Empty Relation 0 NOT == new()") end
if not (r0 == relmetric.Relation:new({})) then fail = true; warn("Empty Relation 0 NOT == new({})") end
if not (r0 == relmetric.Relation:fromints({})) then fail = true; warn("Empty Relation 0 NOT == fromints({})") end
if not (r1[1] == c1) then fail = true; warn("Relation 1[1] NOT == Column 1") end
if not (r1[2] == c0) then fail = true; warn(" Relation 1[2] NOT == Empty Column 0") end
if not (r1 == relmetric.Relation:fromcols(c1, c2)) then fail = true; warn("Relation 1 NOT == fromcols(c1, c2)") end
if not (r2 == relmetric.Relation:fromcols(c3, c4, c5)) then fail = true; warn("Relation 2 NOT == fromcols(c3, c4, c5)") end
if r1[1]:isdisjoint(r2[1]) then fail = true; warn("Relation 1[1] <isdisjoint> Relation 2[1] is NOT false") end
if fail == true then print("> Relation methods: OK\n"); fail = false else print("> Relation methods: fails\n\n") end

-- Test kappa
print("Test kappa")
-- print(string.format("Relation R for E4_8 and E4_9:\n%s", R))
-- print(string.format("E4_8 and 4_9 use Relation:\n%s", R))
if not (E4_8:kappa(5) == 0) then fail = true; warn("Ex 4.8: Kappa(R[2:5], 5) NOT == 0") end
if not (E4_9:kappa(5) == 1) then fail = true; warn("Ex 4_9: Kappa(R[1:5], 5) NOT == 1") end
if not (R:kappa(4) == 1) then fail = true; warn("Ex 4_10: Kappa(R, 4) NOT == 1") end
if not (R:kappa(5) == 3) then fail = true; warn("Ex 4_11: Kappa(R, 5) NOT == 3") end
if fail == true then print("> kappa: OK\n"); fail = false else print("> kappa: fails\n\n") end

-- Test distance bound
print("Test distance bound")
-- local E4_17relmetric, E4_18relmetric = E4_17R1:relmetric(E4_17R2), E4_18R1:relmetric(E4_18R2)
local E4_17rel_dist_bound, E4_18rel_dist_bound = E4_17R1:rel_dist_bound(E4_17R2), E4_18R1:rel_dist_bound(E4_18R2)
-- print(string.format('E4_17: rel_dist_bound(R1, R2) = %s and relmetric(R1, R2) = %s', E4_17rel_dist_bound, E4_17relmetric or "skipped"))
-- print(string.format('E4_18: rel_dist_bound(R1, R2) = %s and relmetric(R1, R2) = %s', E4_18rel_dist_bound, E4_18relmetric or "skipped"))
if not (E4_17rel_dist_bound == 9) then fail = true; warn("Ex 4_17: rel_dist_bound(R1, R2) NOT == 9") end
if not (E4_18rel_dist_bound == 2) then fail = true; warn("Ex 4_18: rel_dist_bound(R1, R2) NOT == 9") end
-- if not (E4_17R1:rel_dist_bound(E4_17R2) == 9) then fail = true; warn("Ex 4_17: rel_dist_bound(R1, R2) NOT == 9") end
-- if not (E4_18R1:rel_dist_bound(E4_18R2) == 2) then fail = true; warn("Ex 4_17: rel_dist_bound(R1, R2) NOT == 9") end
if fail == true then print("> distance bound: OK\n"); fail = false else print("> distance bound: fails\n\n") end

print(string.format("Relation 1:\n%s", r1))
print(string.format("Relation 2:\n%s", r2))
print(string.format("Sorted Relation 2:\n%s", r2:sorted()))
print(string.format("Metric (Relation 1, Relation 2) = %s", r1:relmetric(r2)))
print(string.format("Rel_Dist_Bound (Relation 1, Relation 2) = %s",r1:rel_dist_bound(r2)))
