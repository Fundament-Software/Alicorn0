-- THIS FILE AUTOGENERATED BY terms-gen-meta.lua
---@meta "types.inferrable"

---@class (exact) inferrable: EnumValue
inferrable = {}

---@return boolean
function inferrable:is_bound_variable() end
---@return number
function inferrable:unwrap_bound_variable() end
---@return boolean, number
function inferrable:as_bound_variable() end
---@return boolean
function inferrable:is_typed() end
---@return value, ArrayValue, typed
function inferrable:unwrap_typed() end
---@return boolean, value, ArrayValue, typed
function inferrable:as_typed() end
---@return boolean
function inferrable:is_annotated_lambda() end
---@return string, inferrable, inferrable, Anchor, visibility, checkable
function inferrable:unwrap_annotated_lambda() end
---@return boolean, string, inferrable, inferrable, Anchor, visibility, checkable
function inferrable:as_annotated_lambda() end
---@return boolean
function inferrable:is_pi() end
---@return inferrable, checkable, inferrable, checkable
function inferrable:unwrap_pi() end
---@return boolean, inferrable, checkable, inferrable, checkable
function inferrable:as_pi() end
---@return boolean
function inferrable:is_application() end
---@return inferrable, checkable
function inferrable:unwrap_application() end
---@return boolean, inferrable, checkable
function inferrable:as_application() end
---@return boolean
function inferrable:is_tuple_cons() end
---@return ArrayValue
function inferrable:unwrap_tuple_cons() end
---@return boolean, ArrayValue
function inferrable:as_tuple_cons() end
---@return boolean
function inferrable:is_tuple_elim() end
---@return ArrayValue, inferrable, inferrable
function inferrable:unwrap_tuple_elim() end
---@return boolean, ArrayValue, inferrable, inferrable
function inferrable:as_tuple_elim() end
---@return boolean
function inferrable:is_tuple_type() end
---@return inferrable
function inferrable:unwrap_tuple_type() end
---@return boolean, inferrable
function inferrable:as_tuple_type() end
---@return boolean
function inferrable:is_record_cons() end
---@return MapValue
function inferrable:unwrap_record_cons() end
---@return boolean, MapValue
function inferrable:as_record_cons() end
---@return boolean
function inferrable:is_record_elim() end
---@return inferrable, ArrayValue, inferrable
function inferrable:unwrap_record_elim() end
---@return boolean, inferrable, ArrayValue, inferrable
function inferrable:as_record_elim() end
---@return boolean
function inferrable:is_enum_cons() end
---@return string, inferrable
function inferrable:unwrap_enum_cons() end
---@return boolean, string, inferrable
function inferrable:as_enum_cons() end
---@return boolean
function inferrable:is_enum_elim() end
---@return inferrable, inferrable
function inferrable:unwrap_enum_elim() end
---@return boolean, inferrable, inferrable
function inferrable:as_enum_elim() end
---@return boolean
function inferrable:is_enum_type() end
---@return inferrable
function inferrable:unwrap_enum_type() end
---@return boolean, inferrable
function inferrable:as_enum_type() end
---@return boolean
function inferrable:is_enum_case() end
---@return inferrable, MapValue
function inferrable:unwrap_enum_case() end
---@return boolean, inferrable, MapValue
function inferrable:as_enum_case() end
---@return boolean
function inferrable:is_enum_absurd() end
---@return inferrable, string
function inferrable:unwrap_enum_absurd() end
---@return boolean, inferrable, string
function inferrable:as_enum_absurd() end
---@return boolean
function inferrable:is_object_cons() end
---@return MapValue
function inferrable:unwrap_object_cons() end
---@return boolean, MapValue
function inferrable:as_object_cons() end
---@return boolean
function inferrable:is_object_elim() end
---@return inferrable, inferrable
function inferrable:unwrap_object_elim() end
---@return boolean, inferrable, inferrable
function inferrable:as_object_elim() end
---@return boolean
function inferrable:is_let() end
---@return string, inferrable, inferrable
function inferrable:unwrap_let() end
---@return boolean, string, inferrable, inferrable
function inferrable:as_let() end
---@return boolean
function inferrable:is_operative_cons() end
---@return inferrable, inferrable
function inferrable:unwrap_operative_cons() end
---@return boolean, inferrable, inferrable
function inferrable:as_operative_cons() end
---@return boolean
function inferrable:is_operative_type_cons() end
---@return checkable, inferrable
function inferrable:unwrap_operative_type_cons() end
---@return boolean, checkable, inferrable
function inferrable:as_operative_type_cons() end
---@return boolean
function inferrable:is_level_type() end
---@return nil
function inferrable:unwrap_level_type() end
---@return boolean
function inferrable:as_level_type() end
---@return boolean
function inferrable:is_level0() end
---@return nil
function inferrable:unwrap_level0() end
---@return boolean
function inferrable:as_level0() end
---@return boolean
function inferrable:is_level_suc() end
---@return inferrable
function inferrable:unwrap_level_suc() end
---@return boolean, inferrable
function inferrable:as_level_suc() end
---@return boolean
function inferrable:is_level_max() end
---@return inferrable, inferrable
function inferrable:unwrap_level_max() end
---@return boolean, inferrable, inferrable
function inferrable:as_level_max() end
---@return boolean
function inferrable:is_annotated() end
---@return checkable, inferrable
function inferrable:unwrap_annotated() end
---@return boolean, checkable, inferrable
function inferrable:as_annotated() end
---@return boolean
function inferrable:is_host_tuple_cons() end
---@return ArrayValue
function inferrable:unwrap_host_tuple_cons() end
---@return boolean, ArrayValue
function inferrable:as_host_tuple_cons() end
---@return boolean
function inferrable:is_host_user_defined_type_cons() end
---@return { name: string }, ArrayValue
function inferrable:unwrap_host_user_defined_type_cons() end
---@return boolean, { name: string }, ArrayValue
function inferrable:as_host_user_defined_type_cons() end
---@return boolean
function inferrable:is_host_tuple_type() end
---@return inferrable
function inferrable:unwrap_host_tuple_type() end
---@return boolean, inferrable
function inferrable:as_host_tuple_type() end
---@return boolean
function inferrable:is_host_function_type() end
---@return inferrable, inferrable, checkable
function inferrable:unwrap_host_function_type() end
---@return boolean, inferrable, inferrable, checkable
function inferrable:as_host_function_type() end
---@return boolean
function inferrable:is_host_wrapped_type() end
---@return inferrable
function inferrable:unwrap_host_wrapped_type() end
---@return boolean, inferrable
function inferrable:as_host_wrapped_type() end
---@return boolean
function inferrable:is_host_unstrict_wrapped_type() end
---@return inferrable
function inferrable:unwrap_host_unstrict_wrapped_type() end
---@return boolean, inferrable
function inferrable:as_host_unstrict_wrapped_type() end
---@return boolean
function inferrable:is_host_wrap() end
---@return inferrable
function inferrable:unwrap_host_wrap() end
---@return boolean, inferrable
function inferrable:as_host_wrap() end
---@return boolean
function inferrable:is_host_unstrict_wrap() end
---@return inferrable
function inferrable:unwrap_host_unstrict_wrap() end
---@return boolean, inferrable
function inferrable:as_host_unstrict_wrap() end
---@return boolean
function inferrable:is_host_unwrap() end
---@return inferrable
function inferrable:unwrap_host_unwrap() end
---@return boolean, inferrable
function inferrable:as_host_unwrap() end
---@return boolean
function inferrable:is_host_unstrict_unwrap() end
---@return inferrable
function inferrable:unwrap_host_unstrict_unwrap() end
---@return boolean, inferrable
function inferrable:as_host_unstrict_unwrap() end
---@return boolean
function inferrable:is_host_if() end
---@return checkable, inferrable, inferrable
function inferrable:unwrap_host_if() end
---@return boolean, checkable, inferrable, inferrable
function inferrable:as_host_if() end
---@return boolean
function inferrable:is_host_intrinsic() end
---@return checkable, inferrable, Anchor
function inferrable:unwrap_host_intrinsic() end
---@return boolean, checkable, inferrable, Anchor
function inferrable:as_host_intrinsic() end
---@return boolean
function inferrable:is_program_sequence() end
---@return inferrable, Anchor, inferrable
function inferrable:unwrap_program_sequence() end
---@return boolean, inferrable, Anchor, inferrable
function inferrable:as_program_sequence() end
---@return boolean
function inferrable:is_program_end() end
---@return inferrable
function inferrable:unwrap_program_end() end
---@return boolean, inferrable
function inferrable:as_program_end() end
---@return boolean
function inferrable:is_program_type() end
---@return inferrable, inferrable
function inferrable:unwrap_program_type() end
---@return boolean, inferrable, inferrable
function inferrable:as_program_type() end
---@return boolean
function inferrable:is_hole() end
---@return nil
function inferrable:unwrap_hole() end
---@return boolean
function inferrable:as_hole() end
---@return boolean
function inferrable:is_filled_hole() end
---@return inferrable
function inferrable:unwrap_filled_hole() end
---@return boolean, inferrable
function inferrable:as_filled_hole() end

---@class (exact) inferrableType: EnumType
---@field define_enum fun(self: inferrableType, name: string, variants: Variants): inferrableType
---@field bound_variable fun(index: number): inferrable
---@field typed fun(type: value, usage_counts: ArrayValue, typed_term: typed): inferrable
---@field annotated_lambda fun(param_name: string, param_annotation: inferrable, body: inferrable, anchor: Anchor, visible: visibility, pure: checkable): inferrable
---@field pi fun(param_type: inferrable, param_info: checkable, result_type: inferrable, result_info: checkable): inferrable
---@field application fun(f: inferrable, arg: checkable): inferrable
---@field tuple_cons fun(elements: ArrayValue): inferrable
---@field tuple_elim fun(names: ArrayValue, subject: inferrable, body: inferrable): inferrable
---@field tuple_type fun(desc: inferrable): inferrable
---@field record_cons fun(fields: MapValue): inferrable
---@field record_elim fun(subject: inferrable, field_names: ArrayValue, body: inferrable): inferrable
---@field enum_cons fun(constructor: string, arg: inferrable): inferrable
---@field enum_elim fun(subject: inferrable, mechanism: inferrable): inferrable
---@field enum_type fun(desc: inferrable): inferrable
---@field enum_case fun(target: inferrable, variants: MapValue): inferrable
---@field enum_absurd fun(target: inferrable, debug: string): inferrable
---@field object_cons fun(methods: MapValue): inferrable
---@field object_elim fun(subject: inferrable, mechanism: inferrable): inferrable
---@field let fun(name: string, expr: inferrable, body: inferrable): inferrable
---@field operative_cons fun(operative_type: inferrable, userdata: inferrable): inferrable
---@field operative_type_cons fun(handler: checkable, userdata_type: inferrable): inferrable
---@field level_type inferrable
---@field level0 inferrable
---@field level_suc fun(previous_level: inferrable): inferrable
---@field level_max fun(level_a: inferrable, level_b: inferrable): inferrable
---@field annotated fun(annotated_term: checkable, annotated_type: inferrable): inferrable
---@field host_tuple_cons fun(elements: ArrayValue): inferrable
---@field host_user_defined_type_cons fun(id: { name: string }, family_args: ArrayValue): inferrable
---@field host_tuple_type fun(desc: inferrable): inferrable
---@field host_function_type fun(param_type: inferrable, result_type: inferrable, result_info: checkable): inferrable
---@field host_wrapped_type fun(type: inferrable): inferrable
---@field host_unstrict_wrapped_type fun(type: inferrable): inferrable
---@field host_wrap fun(content: inferrable): inferrable
---@field host_unstrict_wrap fun(content: inferrable): inferrable
---@field host_unwrap fun(container: inferrable): inferrable
---@field host_unstrict_unwrap fun(container: inferrable): inferrable
---@field host_if fun(subject: checkable, consequent: inferrable, alternate: inferrable): inferrable
---@field host_intrinsic fun(source: checkable, type: inferrable, anchor: Anchor): inferrable
---@field program_sequence fun(first: inferrable, anchor: Anchor, continue: inferrable): inferrable
---@field program_end fun(result: inferrable): inferrable
---@field program_type fun(effect_type: inferrable, result_type: inferrable): inferrable
---@field hole inferrable
---@field filled_hole fun(inner: inferrable): inferrable
return {}
