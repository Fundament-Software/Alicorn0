-- THIS FILE AUTOGENERATED BY terms-gen-meta.lua
---@meta "types.block_purity"

---@class (exact) block_purity: EnumValue
block_purity = {}

---@return boolean
function block_purity:is_effectful() end
---@return nil
function block_purity:unwrap_effectful() end
---@return boolean
function block_purity:as_effectful() end
---@return boolean
function block_purity:is_pure() end
---@return nil
function block_purity:unwrap_pure() end
---@return boolean
function block_purity:as_pure() end
---@return boolean
function block_purity:is_dependent() end
---@return value val
function block_purity:unwrap_dependent() end
---@return boolean
---@return value val
function block_purity:as_dependent() end
---@return boolean
function block_purity:is_inherit() end
---@return nil
function block_purity:unwrap_inherit() end
---@return boolean
function block_purity:as_inherit() end

---@class (exact) block_purityType: EnumType
---@field define_enum fun(self: block_purityType, name: string, variants: Variants): block_purityType
---@field effectful block_purity
---@field pure block_purity
---@field dependent fun(val: value): block_purity
---@field inherit block_purity
return {}
