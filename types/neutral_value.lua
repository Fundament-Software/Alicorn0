-- THIS FILE AUTOGENERATED BY terms-gen-meta.lua
---@meta "neutral_value.lua"
---@class (exact) neutral_value
neutral_value = {}
---@return boolean
function neutral_value:is_free() end
---@return free
function neutral_value:unwrap_free() end
---@return boolean
function neutral_value:is_application_stuck() end
---@return neutral_value, value
function neutral_value:unwrap_application_stuck() end
---@return boolean
function neutral_value:is_enum_elim_stuck() end
---@return value, neutral_value
function neutral_value:unwrap_enum_elim_stuck() end
---@return boolean
function neutral_value:is_enum_rec_elim_stuck() end
---@return value, neutral_value
function neutral_value:unwrap_enum_rec_elim_stuck() end
---@return boolean
function neutral_value:is_object_elim_stuck() end
---@return value, neutral_value
function neutral_value:unwrap_object_elim_stuck() end
---@return boolean
function neutral_value:is_tuple_element_access_stuck() end
---@return neutral_value, number
function neutral_value:unwrap_tuple_element_access_stuck() end
---@return boolean
function neutral_value:is_record_field_access_stuck() end
---@return neutral_value, string
function neutral_value:unwrap_record_field_access_stuck() end
---@return boolean
function neutral_value:is_prim_application_stuck() end
---@return any, neutral_value
function neutral_value:unwrap_prim_application_stuck() end
---@return boolean
function neutral_value:is_prim_tuple_stuck() end
---@return any, neutral_value, any
function neutral_value:unwrap_prim_tuple_stuck() end
---@return boolean
function neutral_value:is_prim_if_stuck() end
---@return neutral_value, value, value
function neutral_value:unwrap_prim_if_stuck() end
---@return boolean
function neutral_value:is_prim_intrinsic_stuck() end
---@return neutral_value, any
function neutral_value:unwrap_prim_intrinsic_stuck() end
---@return boolean
function neutral_value:is_prim_wrap_stuck() end
---@return neutral_value
function neutral_value:unwrap_prim_wrap_stuck() end
---@return boolean
function neutral_value:is_prim_unwrap_stuck() end
---@return neutral_value
function neutral_value:unwrap_prim_unwrap_stuck() end
---@class (exact) neutral_valueType:Type
---@field free fun(free:free): neutral_value
---@field application_stuck fun(f:neutral_value, arg:value): neutral_value
---@field enum_elim_stuck fun(mechanism:value, subject:neutral_value): neutral_value
---@field enum_rec_elim_stuck fun(handler:value, subject:neutral_value): neutral_value
---@field object_elim_stuck fun(mechanism:value, subject:neutral_value): neutral_value
---@field tuple_element_access_stuck fun(subject:neutral_value, index:number): neutral_value
---@field record_field_access_stuck fun(subject:neutral_value, field_name:string): neutral_value
---@field prim_application_stuck fun(function:any, arg:neutral_value): neutral_value
---@field prim_tuple_stuck fun(leading:any, stuck_element:neutral_value, trailing:any): neutral_value
---@field prim_if_stuck fun(subject:neutral_value, consequent:value, alternate:value): neutral_value
---@field prim_intrinsic_stuck fun(source:neutral_value, anchor:any): neutral_value
---@field prim_wrap_stuck fun(content:neutral_value): neutral_value
---@field prim_unwrap_stuck fun(container:neutral_value): neutral_value
return {}