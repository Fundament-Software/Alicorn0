-- THIS FILE AUTOGENERATED BY terms-gen-meta.lua
---@meta "types.neutral_value"

---@class (exact) neutral_value: EnumValue
neutral_value = {}

---@return boolean
function neutral_value:is_free() end
---@return free
function neutral_value:unwrap_free() end
---@return boolean, free
function neutral_value:as_free() end
---@return boolean
function neutral_value:is_application_stuck() end
---@return neutral_value, value
function neutral_value:unwrap_application_stuck() end
---@return boolean, neutral_value, value
function neutral_value:as_application_stuck() end
---@return boolean
function neutral_value:is_enum_elim_stuck() end
---@return value, neutral_value
function neutral_value:unwrap_enum_elim_stuck() end
---@return boolean, value, neutral_value
function neutral_value:as_enum_elim_stuck() end
---@return boolean
function neutral_value:is_enum_rec_elim_stuck() end
---@return value, neutral_value
function neutral_value:unwrap_enum_rec_elim_stuck() end
---@return boolean, value, neutral_value
function neutral_value:as_enum_rec_elim_stuck() end
---@return boolean
function neutral_value:is_object_elim_stuck() end
---@return value, neutral_value
function neutral_value:unwrap_object_elim_stuck() end
---@return boolean, value, neutral_value
function neutral_value:as_object_elim_stuck() end
---@return boolean
function neutral_value:is_tuple_element_access_stuck() end
---@return neutral_value, number
function neutral_value:unwrap_tuple_element_access_stuck() end
---@return boolean, neutral_value, number
function neutral_value:as_tuple_element_access_stuck() end
---@return boolean
function neutral_value:is_record_field_access_stuck() end
---@return neutral_value, string
function neutral_value:unwrap_record_field_access_stuck() end
---@return boolean, neutral_value, string
function neutral_value:as_record_field_access_stuck() end
---@return boolean
function neutral_value:is_host_application_stuck() end
---@return any, neutral_value
function neutral_value:unwrap_host_application_stuck() end
---@return boolean, any, neutral_value
function neutral_value:as_host_application_stuck() end
---@return boolean
function neutral_value:is_host_tuple_stuck() end
---@return ArrayValue, neutral_value, ArrayValue
function neutral_value:unwrap_host_tuple_stuck() end
---@return boolean, ArrayValue, neutral_value, ArrayValue
function neutral_value:as_host_tuple_stuck() end
---@return boolean
function neutral_value:is_host_if_stuck() end
---@return neutral_value, value, value
function neutral_value:unwrap_host_if_stuck() end
---@return boolean, neutral_value, value, value
function neutral_value:as_host_if_stuck() end
---@return boolean
function neutral_value:is_host_intrinsic_stuck() end
---@return neutral_value, Anchor
function neutral_value:unwrap_host_intrinsic_stuck() end
---@return boolean, neutral_value, Anchor
function neutral_value:as_host_intrinsic_stuck() end
---@return boolean
function neutral_value:is_host_wrap_stuck() end
---@return neutral_value
function neutral_value:unwrap_host_wrap_stuck() end
---@return boolean, neutral_value
function neutral_value:as_host_wrap_stuck() end
---@return boolean
function neutral_value:is_host_unwrap_stuck() end
---@return neutral_value
function neutral_value:unwrap_host_unwrap_stuck() end
---@return boolean, neutral_value
function neutral_value:as_host_unwrap_stuck() end
---@return boolean
function neutral_value:is_checkable_hole() end
---@return value
function neutral_value:unwrap_checkable_hole() end
---@return boolean, value
function neutral_value:as_checkable_hole() end
---@return boolean
function neutral_value:is_checkable_filled_hole() end
---@return value, value, value
function neutral_value:unwrap_checkable_filled_hole() end
---@return boolean, value, value, value
function neutral_value:as_checkable_filled_hole() end
---@return boolean
function neutral_value:is_inferrable_hole() end
---@return nil
function neutral_value:unwrap_inferrable_hole() end
---@return boolean
function neutral_value:as_inferrable_hole() end
---@return boolean
function neutral_value:is_inferrable_filled_hole() end
---@return value, value
function neutral_value:unwrap_inferrable_filled_hole() end
---@return boolean, value, value
function neutral_value:as_inferrable_filled_hole() end

---@class (exact) neutral_valueType: EnumType
---@field define_enum fun(self: neutral_valueType, name: string, variants: Variants): neutral_valueType
---@field free fun(free: free): neutral_value
---@field application_stuck fun(f: neutral_value, arg: value): neutral_value
---@field enum_elim_stuck fun(mechanism: value, subject: neutral_value): neutral_value
---@field enum_rec_elim_stuck fun(handler: value, subject: neutral_value): neutral_value
---@field object_elim_stuck fun(mechanism: value, subject: neutral_value): neutral_value
---@field tuple_element_access_stuck fun(subject: neutral_value, index: number): neutral_value
---@field record_field_access_stuck fun(subject: neutral_value, field_name: string): neutral_value
---@field host_application_stuck fun(function: any, arg: neutral_value): neutral_value
---@field host_tuple_stuck fun(leading: ArrayValue, stuck_element: neutral_value, trailing: ArrayValue): neutral_value
---@field host_if_stuck fun(subject: neutral_value, consequent: value, alternate: value): neutral_value
---@field host_intrinsic_stuck fun(source: neutral_value, anchor: Anchor): neutral_value
---@field host_wrap_stuck fun(content: neutral_value): neutral_value
---@field host_unwrap_stuck fun(container: neutral_value): neutral_value
---@field checkable_hole fun(goal_type: value): neutral_value
---@field checkable_filled_hole fun(inner_type: value, inner_val: value, goal_type: value): neutral_value
---@field inferrable_hole neutral_value
---@field inferrable_filled_hole fun(inner_type: value, inner_val: value): neutral_value
return {}
