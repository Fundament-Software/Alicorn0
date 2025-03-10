-- THIS FILE AUTOGENERATED BY terms-gen-meta.lua
---@meta "types.flex_value"

---@class (exact) flex_value: EnumValue
flex_value = {}

---@return boolean
function flex_value:is_strict() end
---@return strict_value strict
function flex_value:unwrap_strict() end
---@return boolean
---@return strict_value strict
function flex_value:as_strict() end
---@return boolean
function flex_value:is_stuck() end
---@return stuck_value stuck
function flex_value:unwrap_stuck() end
---@return boolean
---@return stuck_value stuck
function flex_value:as_stuck() end
---@return boolean
function flex_value:is_visibility_type() end
---@return nil
function flex_value:unwrap_visibility_type() end
---@return boolean
function flex_value:as_visibility_type() end
---@return boolean
function flex_value:is_visibility() end
---@return visibility visibility
function flex_value:unwrap_visibility() end
---@return boolean
---@return visibility visibility
function flex_value:as_visibility() end
---@return boolean
function flex_value:is_param_info_type() end
---@return nil
function flex_value:unwrap_param_info_type() end
---@return boolean
function flex_value:as_param_info_type() end
---@return boolean
function flex_value:is_param_info() end
---@return flex_value visibility
function flex_value:unwrap_param_info() end
---@return boolean
---@return flex_value visibility
function flex_value:as_param_info() end
---@return boolean
function flex_value:is_result_info_type() end
---@return nil
function flex_value:unwrap_result_info_type() end
---@return boolean
function flex_value:as_result_info_type() end
---@return boolean
function flex_value:is_result_info() end
---@return result_info result_info
function flex_value:unwrap_result_info() end
---@return boolean
---@return result_info result_info
function flex_value:as_result_info() end
---@return boolean
function flex_value:is_pi() end
---@return flex_value param_type
---@return flex_value param_info
---@return flex_value result_type
---@return flex_value result_info
function flex_value:unwrap_pi() end
---@return boolean
---@return flex_value param_type
---@return flex_value param_info
---@return flex_value result_type
---@return flex_value result_info
function flex_value:as_pi() end
---@return boolean
function flex_value:is_closure() end
---@return string param_name
---@return typed code
---@return flex_value capture
---@return spanned_name capture_dbg
---@return spanned_name param_debug
function flex_value:unwrap_closure() end
---@return boolean
---@return string param_name
---@return typed code
---@return flex_value capture
---@return spanned_name capture_dbg
---@return spanned_name param_debug
function flex_value:as_closure() end
---@return boolean
function flex_value:is_range() end
---@return ArrayValue<flex_value> lower_bounds
---@return ArrayValue<flex_value> upper_bounds
---@return strict_value relation
function flex_value:unwrap_range() end
---@return boolean
---@return ArrayValue<flex_value> lower_bounds
---@return ArrayValue<flex_value> upper_bounds
---@return strict_value relation
function flex_value:as_range() end
---@return boolean
function flex_value:is_name_type() end
---@return nil
function flex_value:unwrap_name_type() end
---@return boolean
function flex_value:as_name_type() end
---@return boolean
function flex_value:is_name() end
---@return string name
function flex_value:unwrap_name() end
---@return boolean
---@return string name
function flex_value:as_name() end
---@return boolean
function flex_value:is_name_set() end
---@return string names
function flex_value:unwrap_name_set() end
---@return boolean
---@return string names
function flex_value:as_name_set() end
---@return boolean
function flex_value:is_name_set_type() end
---@return nil
function flex_value:unwrap_name_set_type() end
---@return boolean
function flex_value:as_name_set_type() end
---@return boolean
function flex_value:is_name_set_of_record_desc() end
---@return stuck_value desc
function flex_value:unwrap_name_set_of_record_desc() end
---@return boolean
---@return stuck_value desc
function flex_value:as_name_set_of_record_desc() end
---@return boolean
function flex_value:is_noncolliding_name_type() end
---@return flex_value set
function flex_value:unwrap_noncolliding_name_type() end
---@return boolean
---@return flex_value set
function flex_value:as_noncolliding_name_type() end
---@return boolean
function flex_value:is_operative_value() end
---@return flex_value userdata
function flex_value:unwrap_operative_value() end
---@return boolean
---@return flex_value userdata
function flex_value:as_operative_value() end
---@return boolean
function flex_value:is_operative_type() end
---@return flex_value handler
---@return flex_value userdata_type
function flex_value:unwrap_operative_type() end
---@return boolean
---@return flex_value handler
---@return flex_value userdata_type
function flex_value:as_operative_type() end
---@return boolean
function flex_value:is_tuple_value() end
---@return ArrayValue<flex_value> elements
function flex_value:unwrap_tuple_value() end
---@return boolean
---@return ArrayValue<flex_value> elements
function flex_value:as_tuple_value() end
---@return boolean
function flex_value:is_tuple_type() end
---@return flex_value desc
function flex_value:unwrap_tuple_type() end
---@return boolean
---@return flex_value desc
function flex_value:as_tuple_type() end
---@return boolean
function flex_value:is_tuple_desc_type() end
---@return flex_value universe
function flex_value:unwrap_tuple_desc_type() end
---@return boolean
---@return flex_value universe
function flex_value:as_tuple_desc_type() end
---@return boolean
function flex_value:is_tuple_desc_concat_indep() end
---@return flex_value prefix
---@return flex_value suffix
function flex_value:unwrap_tuple_desc_concat_indep() end
---@return boolean
---@return flex_value prefix
---@return flex_value suffix
function flex_value:as_tuple_desc_concat_indep() end
---@return boolean
function flex_value:is_enum_value() end
---@return string constructor
---@return flex_value arg
function flex_value:unwrap_enum_value() end
---@return boolean
---@return string constructor
---@return flex_value arg
function flex_value:as_enum_value() end
---@return boolean
function flex_value:is_enum_type() end
---@return flex_value desc
function flex_value:unwrap_enum_type() end
---@return boolean
---@return flex_value desc
function flex_value:as_enum_type() end
---@return boolean
function flex_value:is_enum_desc_type() end
---@return flex_value universe
function flex_value:unwrap_enum_desc_type() end
---@return boolean
---@return flex_value universe
function flex_value:as_enum_desc_type() end
---@return boolean
function flex_value:is_enum_desc_value() end
---@return MapValue<string, flex_value> variants
function flex_value:unwrap_enum_desc_value() end
---@return boolean
---@return MapValue<string, flex_value> variants
function flex_value:as_enum_desc_value() end
---@return boolean
function flex_value:is_record_value() end
---@return MapValue<string, flex_value> fields
function flex_value:unwrap_record_value() end
---@return boolean
---@return MapValue<string, flex_value> fields
function flex_value:as_record_value() end
---@return boolean
function flex_value:is_record_type() end
---@return flex_value desc
function flex_value:unwrap_record_type() end
---@return boolean
---@return flex_value desc
function flex_value:as_record_type() end
---@return boolean
function flex_value:is_record_desc_type() end
---@return flex_value universe
function flex_value:unwrap_record_desc_type() end
---@return boolean
---@return flex_value universe
function flex_value:as_record_desc_type() end
---@return boolean
function flex_value:is_record_desc_value() end
---@return MapValue<string, flex_value> fields
function flex_value:unwrap_record_desc_value() end
---@return boolean
---@return MapValue<string, flex_value> fields
function flex_value:as_record_desc_value() end
---@return boolean
function flex_value:is_record_desc_extend_single() end
---@return flex_value base
---@return stuck_value name
---@return flex_value typefn
function flex_value:unwrap_record_desc_extend_single() end
---@return boolean
---@return flex_value base
---@return stuck_value name
---@return flex_value typefn
function flex_value:as_record_desc_extend_single() end
---@return boolean
function flex_value:is_record_desc_extend() end
---@return flex_value base
---@return MapValue<string, flex_value> extension
function flex_value:unwrap_record_desc_extend() end
---@return boolean
---@return flex_value base
---@return MapValue<string, flex_value> extension
function flex_value:as_record_desc_extend() end
---@return boolean
function flex_value:is_record_extend_single() end
---@return flex_value base
---@return stuck_value name
---@return flex_value val
function flex_value:unwrap_record_extend_single() end
---@return boolean
---@return flex_value base
---@return stuck_value name
---@return flex_value val
function flex_value:as_record_extend_single() end
---@return boolean
function flex_value:is_record_extend() end
---@return stuck_value base
---@return MapValue<string, flex_value> extension
function flex_value:unwrap_record_extend() end
---@return boolean
---@return stuck_value base
---@return MapValue<string, flex_value> extension
function flex_value:as_record_extend() end
---@return boolean
function flex_value:is_object_value() end
---@return MapValue<string, typed> methods
---@return FlexRuntimeContext capture
function flex_value:unwrap_object_value() end
---@return boolean
---@return MapValue<string, typed> methods
---@return FlexRuntimeContext capture
function flex_value:as_object_value() end
---@return boolean
function flex_value:is_object_type() end
---@return flex_value desc
function flex_value:unwrap_object_type() end
---@return boolean
---@return flex_value desc
function flex_value:as_object_type() end
---@return boolean
function flex_value:is_star() end
---@return integer level
---@return integer depth
function flex_value:unwrap_star() end
---@return boolean
---@return integer level
---@return integer depth
function flex_value:as_star() end
---@return boolean
function flex_value:is_prop() end
---@return integer level
function flex_value:unwrap_prop() end
---@return boolean
---@return integer level
function flex_value:as_prop() end
---@return boolean
function flex_value:is_host_value() end
---@return any host_value
function flex_value:unwrap_host_value() end
---@return boolean
---@return any host_value
function flex_value:as_host_value() end
---@return boolean
function flex_value:is_host_type_type() end
---@return nil
function flex_value:unwrap_host_type_type() end
---@return boolean
function flex_value:as_host_type_type() end
---@return boolean
function flex_value:is_host_number_type() end
---@return nil
function flex_value:unwrap_host_number_type() end
---@return boolean
function flex_value:as_host_number_type() end
---@return boolean
function flex_value:is_host_int_fold() end
---@return stuck_value num
---@return flex_value f
---@return flex_value acc
function flex_value:unwrap_host_int_fold() end
---@return boolean
---@return stuck_value num
---@return flex_value f
---@return flex_value acc
function flex_value:as_host_int_fold() end
---@return boolean
function flex_value:is_host_bool_type() end
---@return nil
function flex_value:unwrap_host_bool_type() end
---@return boolean
function flex_value:as_host_bool_type() end
---@return boolean
function flex_value:is_host_string_type() end
---@return nil
function flex_value:unwrap_host_string_type() end
---@return boolean
function flex_value:as_host_string_type() end
---@return boolean
function flex_value:is_host_function_type() end
---@return flex_value param_type
---@return flex_value result_type
---@return flex_value result_info
function flex_value:unwrap_host_function_type() end
---@return boolean
---@return flex_value param_type
---@return flex_value result_type
---@return flex_value result_info
function flex_value:as_host_function_type() end
---@return boolean
function flex_value:is_host_wrapped_type() end
---@return flex_value type
function flex_value:unwrap_host_wrapped_type() end
---@return boolean
---@return flex_value type
function flex_value:as_host_wrapped_type() end
---@return boolean
function flex_value:is_host_unstrict_wrapped_type() end
---@return flex_value type
function flex_value:unwrap_host_unstrict_wrapped_type() end
---@return boolean
---@return flex_value type
function flex_value:as_host_unstrict_wrapped_type() end
---@return boolean
function flex_value:is_host_user_defined_type() end
---@return { name: string } id
---@return ArrayValue<flex_value> family_args
function flex_value:unwrap_host_user_defined_type() end
---@return boolean
---@return { name: string } id
---@return ArrayValue<flex_value> family_args
function flex_value:as_host_user_defined_type() end
---@return boolean
function flex_value:is_host_nil_type() end
---@return nil
function flex_value:unwrap_host_nil_type() end
---@return boolean
function flex_value:as_host_nil_type() end
---@return boolean
function flex_value:is_host_tuple_value() end
---@return ArrayValue<any> elements
function flex_value:unwrap_host_tuple_value() end
---@return boolean
---@return ArrayValue<any> elements
function flex_value:as_host_tuple_value() end
---@return boolean
function flex_value:is_host_tuple_type() end
---@return flex_value desc
function flex_value:unwrap_host_tuple_type() end
---@return boolean
---@return flex_value desc
function flex_value:as_host_tuple_type() end
---@return boolean
function flex_value:is_singleton() end
---@return flex_value supertype
---@return flex_value value
function flex_value:unwrap_singleton() end
---@return boolean
---@return flex_value supertype
---@return flex_value value
function flex_value:as_singleton() end
---@return boolean
function flex_value:is_program_end() end
---@return flex_value result
function flex_value:unwrap_program_end() end
---@return boolean
---@return flex_value result
function flex_value:as_program_end() end
---@return boolean
function flex_value:is_program_cont() end
---@return table action
---@return flex_value argument
---@return flex_continuation continuation
function flex_value:unwrap_program_cont() end
---@return boolean
---@return table action
---@return flex_value argument
---@return flex_continuation continuation
function flex_value:as_program_cont() end
---@return boolean
function flex_value:is_effect_elem() end
---@return effect_id tag
function flex_value:unwrap_effect_elem() end
---@return boolean
---@return effect_id tag
function flex_value:as_effect_elem() end
---@return boolean
function flex_value:is_effect_type() end
---@return nil
function flex_value:unwrap_effect_type() end
---@return boolean
function flex_value:as_effect_type() end
---@return boolean
function flex_value:is_effect_row() end
---@return SetValue<table> components
function flex_value:unwrap_effect_row() end
---@return boolean
---@return SetValue<table> components
function flex_value:as_effect_row() end
---@return boolean
function flex_value:is_effect_row_extend() end
---@return flex_value base
---@return flex_value rest
function flex_value:unwrap_effect_row_extend() end
---@return boolean
---@return flex_value base
---@return flex_value rest
function flex_value:as_effect_row_extend() end
---@return boolean
function flex_value:is_effect_row_type() end
---@return nil
function flex_value:unwrap_effect_row_type() end
---@return boolean
function flex_value:as_effect_row_type() end
---@return boolean
function flex_value:is_program_type() end
---@return flex_value effect_sig
---@return flex_value base_type
function flex_value:unwrap_program_type() end
---@return boolean
---@return flex_value effect_sig
---@return flex_value base_type
function flex_value:as_program_type() end
---@return boolean
function flex_value:is_srel_type() end
---@return flex_value target_type
function flex_value:unwrap_srel_type() end
---@return boolean
---@return flex_value target_type
function flex_value:as_srel_type() end
---@return boolean
function flex_value:is_variance_type() end
---@return flex_value target_type
function flex_value:unwrap_variance_type() end
---@return boolean
---@return flex_value target_type
function flex_value:as_variance_type() end
---@return boolean
function flex_value:is_intersection_type() end
---@return flex_value left
---@return flex_value right
function flex_value:unwrap_intersection_type() end
---@return boolean
---@return flex_value left
---@return flex_value right
function flex_value:as_intersection_type() end
---@return boolean
function flex_value:is_union_type() end
---@return flex_value left
---@return flex_value right
function flex_value:unwrap_union_type() end
---@return boolean
---@return flex_value left
---@return flex_value right
function flex_value:as_union_type() end
---@return boolean
function flex_value:is_free() end
---@return free free
function flex_value:unwrap_free() end
---@return boolean
---@return free free
function flex_value:as_free() end
---@return boolean
function flex_value:is_application() end
---@return stuck_value f
---@return flex_value arg
function flex_value:unwrap_application() end
---@return boolean
---@return stuck_value f
---@return flex_value arg
function flex_value:as_application() end
---@return boolean
function flex_value:is_tuple_element_access() end
---@return stuck_value subject
---@return integer index
function flex_value:unwrap_tuple_element_access() end
---@return boolean
---@return stuck_value subject
---@return integer index
function flex_value:as_tuple_element_access() end
---@return boolean
function flex_value:is_record_field_access() end
---@return stuck_value subject
---@return string field_name
function flex_value:unwrap_record_field_access() end
---@return boolean
---@return stuck_value subject
---@return string field_name
function flex_value:as_record_field_access() end
---@return boolean
function flex_value:is_host_application() end
---@return any function
---@return stuck_value arg
function flex_value:unwrap_host_application() end
---@return boolean
---@return any function
---@return stuck_value arg
function flex_value:as_host_application() end
---@return boolean
function flex_value:is_host_tuple() end
---@return ArrayValue<any> leading
---@return stuck_value stuck_element
---@return ArrayValue<flex_value> trailing
function flex_value:unwrap_host_tuple() end
---@return boolean
---@return ArrayValue<any> leading
---@return stuck_value stuck_element
---@return ArrayValue<flex_value> trailing
function flex_value:as_host_tuple() end
---@return boolean
function flex_value:is_host_if() end
---@return stuck_value subject
---@return flex_value consequent
---@return flex_value alternate
function flex_value:unwrap_host_if() end
---@return boolean
---@return stuck_value subject
---@return flex_value consequent
---@return flex_value alternate
function flex_value:as_host_if() end
---@return boolean
function flex_value:is_host_intrinsic() end
---@return stuck_value source
---@return Anchor start_anchor
function flex_value:unwrap_host_intrinsic() end
---@return boolean
---@return stuck_value source
---@return Anchor start_anchor
function flex_value:as_host_intrinsic() end
---@return boolean
function flex_value:is_host_wrap() end
---@return stuck_value content
function flex_value:unwrap_host_wrap() end
---@return boolean
---@return stuck_value content
function flex_value:as_host_wrap() end
---@return boolean
function flex_value:is_host_unwrap() end
---@return stuck_value container
function flex_value:unwrap_host_unwrap() end
---@return boolean
---@return stuck_value container
function flex_value:as_host_unwrap() end

---@class (exact) flex_valueType: EnumType
---@field define_enum fun(self: flex_valueType, name: string, variants: Variants): flex_valueType
---@field strict fun(strict: strict_value): flex_value
---@field stuck fun(stuck: stuck_value): flex_value
---@field visibility_type flex_value
---@field visibility fun(visibility: visibility): flex_value
---@field param_info_type flex_value
---@field param_info fun(visibility: flex_value): flex_value
---@field result_info_type flex_value
---@field result_info fun(result_info: result_info): flex_value
---@field pi fun(param_type: flex_value, param_info: flex_value, result_type: flex_value, result_info: flex_value): flex_value
---@field closure fun(param_name: string, code: typed, capture: flex_value, capture_dbg: spanned_name, param_debug: spanned_name): flex_value
---@field range fun(lower_bounds: ArrayValue<flex_value>, upper_bounds: ArrayValue<flex_value>, relation: strict_value): flex_value
---@field name_type flex_value
---@field name fun(name: string): flex_value
---@field name_set fun(names: string): flex_value
---@field name_set_type flex_value
---@field name_set_of_record_desc fun(desc: stuck_value): flex_value
---@field noncolliding_name_type fun(set: flex_value): flex_value
---@field operative_value fun(userdata: flex_value): flex_value
---@field operative_type fun(handler: flex_value, userdata_type: flex_value): flex_value
---@field tuple_value fun(elements: ArrayValue<flex_value>): flex_value
---@field tuple_type fun(desc: flex_value): flex_value
---@field tuple_desc_type fun(universe: flex_value): flex_value
---@field tuple_desc_concat_indep fun(prefix: flex_value, suffix: flex_value): flex_value
---@field enum_value fun(constructor: string, arg: flex_value): flex_value
---@field enum_type fun(desc: flex_value): flex_value
---@field enum_desc_type fun(universe: flex_value): flex_value
---@field enum_desc_value fun(variants: MapValue<string, flex_value>): flex_value
---@field record_value fun(fields: MapValue<string, flex_value>): flex_value
---@field record_type fun(desc: flex_value): flex_value
---@field record_desc_type fun(universe: flex_value): flex_value
---@field record_desc_value fun(fields: MapValue<string, flex_value>): flex_value
---@field record_desc_extend_single fun(base: flex_value, name: stuck_value, typefn: flex_value): flex_value
---@field record_desc_extend fun(base: flex_value, extension: MapValue<string, flex_value>): flex_value
---@field record_extend_single fun(base: flex_value, name: stuck_value, val: flex_value): flex_value
---@field record_extend fun(base: stuck_value, extension: MapValue<string, flex_value>): flex_value
---@field object_value fun(methods: MapValue<string, typed>, capture: FlexRuntimeContext): flex_value
---@field object_type fun(desc: flex_value): flex_value
---@field star fun(level: integer, depth: integer): flex_value
---@field prop fun(level: integer): flex_value
---@field host_value fun(host_value: any): flex_value
---@field host_type_type flex_value
---@field host_number_type flex_value
---@field host_int_fold fun(num: stuck_value, f: flex_value, acc: flex_value): flex_value
---@field host_bool_type flex_value
---@field host_string_type flex_value
---@field host_function_type fun(param_type: flex_value, result_type: flex_value, result_info: flex_value): flex_value
---@field host_wrapped_type fun(type: flex_value): flex_value
---@field host_unstrict_wrapped_type fun(type: flex_value): flex_value
---@field host_user_defined_type fun(id: { name: string }, family_args: ArrayValue<flex_value>): flex_value
---@field host_nil_type flex_value
---@field host_tuple_value fun(elements: ArrayValue<any>): flex_value
---@field host_tuple_type fun(desc: flex_value): flex_value
---@field singleton fun(supertype: flex_value, value: flex_value): flex_value
---@field program_end fun(result: flex_value): flex_value
---@field program_cont fun(action: table, argument: flex_value, continuation: flex_continuation): flex_value
---@field effect_elem fun(tag: effect_id): flex_value
---@field effect_type flex_value
---@field effect_row fun(components: SetValue<table>): flex_value
---@field effect_row_extend fun(base: flex_value, rest: flex_value): flex_value
---@field effect_row_type flex_value
---@field program_type fun(effect_sig: flex_value, base_type: flex_value): flex_value
---@field srel_type fun(target_type: flex_value): flex_value
---@field variance_type fun(target_type: flex_value): flex_value
---@field intersection_type fun(left: flex_value, right: flex_value): flex_value
---@field union_type fun(left: flex_value, right: flex_value): flex_value
---@field free fun(free: free): flex_value
---@field application fun(f: stuck_value, arg: flex_value): flex_value
---@field tuple_element_access fun(subject: stuck_value, index: integer): flex_value
---@field record_field_access fun(subject: stuck_value, field_name: string): flex_value
---@field host_application fun(function: any, arg: stuck_value): flex_value
---@field host_tuple fun(leading: ArrayValue<any>, stuck_element: stuck_value, trailing: ArrayValue<flex_value>): flex_value
---@field host_if fun(subject: stuck_value, consequent: flex_value, alternate: flex_value): flex_value
---@field host_intrinsic fun(source: stuck_value, start_anchor: Anchor): flex_value
---@field host_wrap fun(content: stuck_value): flex_value
---@field host_unwrap fun(container: stuck_value): flex_value
return {}
