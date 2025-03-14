-- THIS FILE AUTOGENERATED BY terms-gen-meta.lua
---@meta "types.tristate"

---@class (exact) tristate: EnumValue
tristate = {}

---@return boolean
function tristate:is_success() end
---@return nil
function tristate:unwrap_success() end
---@return boolean
function tristate:as_success() end
---@return boolean
function tristate:is_continue() end
---@return nil
function tristate:unwrap_continue() end
---@return boolean
function tristate:as_continue() end
---@return boolean
function tristate:is_failure() end
---@return nil
function tristate:unwrap_failure() end
---@return boolean
function tristate:as_failure() end

---@class (exact) tristateType: EnumType
---@field define_enum fun(self: tristateType, name: string, variants: Variants): tristateType
---@field success tristate
---@field continue tristate
---@field failure tristate
return {}
