-- THIS FILE AUTOGENERATED BY terms-gen-meta.lua
---@meta "purity.lua"
---@class (exact) purity
---@field kind string
---@field pretty_print fun(...)
purity = {}
---@return boolean
function purity:is_effectful() end
---@return boolean
function purity:is_pure() end
---@class (exact) purityType:Type
---@field effectful purity
---@field pure purity
return {}
