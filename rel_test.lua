#! /usr/bin/env lua

--[[
  rel_test
--]]

DEBUG = false

local RM = require("relmetric")

local r1 = RM.Relation:new({
  row_count = 32,
  column_count = 2,
  bitfield = {
    RM.Column:fromints(0x3000, 0x000f),
    RM.Column:fromints(0x0000, 0x0000)
  }
})
local r2 = RM.Relation:new({
  row_count = 32,
  column_count = 3,
  bitfield = {
    RM.Column:fromints(0x100f, 0x0f3f),
    RM.Column:fromints(0x0000, 0x000f),
    RM.Column:fromints(0x0000, 0x0010)
  }
})
print("Relation 1:")
print(r1)
print("")
print("Relation 2:")
print(r2)
print("")
print("Metric = "..tostring(r1:relmetric(r2)))
