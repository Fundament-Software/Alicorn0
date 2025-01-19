-- THIS FILE AUTOGENERATED BY terms-gen-meta.lua
---@meta "types.typed"

---@class (exact) typed: EnumValue
typed = {}

---@return boolean
function typed:is_bound_variable() end
---@return number index
---@return any debug
function typed:unwrap_bound_variable() end
---@return boolean
---@return number index
---@return any debug
function typed:as_bound_variable() end
---@return boolean
function typed:is_literal() end
---@return value literal_value
function typed:unwrap_literal() end
---@return boolean
---@return value literal_value
function typed:as_literal() end
---@return boolean
function typed:is_lambda() end
---@return string param_name
---@return typed body
---@return Anchor start_anchor
function typed:unwrap_lambda() end
---@return boolean
---@return string param_name
---@return typed body
---@return Anchor start_anchor
function typed:as_lambda() end
---@return boolean
function typed:is_pi() end
---@return typed param_type
---@return typed param_info
---@return typed result_type
---@return typed result_info
function typed:unwrap_pi() end
---@return boolean
---@return typed param_type
---@return typed param_info
---@return typed result_type
---@return typed result_info
function typed:as_pi() end
---@return boolean
function typed:is_application() end
---@return typed f
---@return typed arg
function typed:unwrap_application() end
---@return boolean
---@return typed f
---@return typed arg
function typed:as_application() end
---@return boolean
function typed:is_let() end
---@return string name
---@return typed expr
---@return typed body
function typed:unwrap_let() end
---@return boolean
---@return string name
---@return typed expr
---@return typed body
function typed:as_let() end
---@return boolean
function typed:is_level_type() end
---@return nil
function typed:unwrap_level_type() end
---@return boolean
function typed:as_level_type() end
---@return boolean
function typed:is_level0() end
---@return nil
function typed:unwrap_level0() end
---@return boolean
function typed:as_level0() end
---@return boolean
function typed:is_level_suc() end
---@return typed previous_level
function typed:unwrap_level_suc() end
---@return boolean
---@return typed previous_level
function typed:as_level_suc() end
---@return boolean
function typed:is_level_max() end
---@return typed level_a
---@return typed level_b
function typed:unwrap_level_max() end
---@return boolean
---@return typed level_a
---@return typed level_b
function typed:as_level_max() end
---@return boolean
function typed:is_star() end
---@return number level
---@return number depth
function typed:unwrap_star() end
---@return boolean
---@return number level
---@return number depth
function typed:as_star() end
---@return boolean
function typed:is_prop() end
---@return number level
function typed:unwrap_prop() end
---@return boolean
---@return number level
function typed:as_prop() end
---@return boolean
function typed:is_tuple_cons() end
---@return ArrayValue elements
function typed:unwrap_tuple_cons() end
---@return boolean
---@return ArrayValue elements
function typed:as_tuple_cons() end
---@return boolean
function typed:is_tuple_elim() end
---@return ArrayValue names
---@return typed subject
---@return number length
---@return typed body
function typed:unwrap_tuple_elim() end
---@return boolean
---@return ArrayValue names
---@return typed subject
---@return number length
---@return typed body
function typed:as_tuple_elim() end
---@return boolean
function typed:is_tuple_element_access() end
---@return typed subject
---@return number index
function typed:unwrap_tuple_element_access() end
---@return boolean
---@return typed subject
---@return number index
function typed:as_tuple_element_access() end
---@return boolean
function typed:is_tuple_type() end
---@return typed desc
function typed:unwrap_tuple_type() end
---@return boolean
---@return typed desc
function typed:as_tuple_type() end
---@return boolean
function typed:is_tuple_desc_type() end
---@return typed universe
function typed:unwrap_tuple_desc_type() end
---@return boolean
---@return typed universe
function typed:as_tuple_desc_type() end
---@return boolean
function typed:is_record_cons() end
---@return MapValue fields
function typed:unwrap_record_cons() end
---@return boolean
---@return MapValue fields
function typed:as_record_cons() end
---@return boolean
function typed:is_record_extend() end
---@return typed base
---@return MapValue fields
function typed:unwrap_record_extend() end
---@return boolean
---@return typed base
---@return MapValue fields
function typed:as_record_extend() end
---@return boolean
function typed:is_record_elim() end
---@return typed subject
---@return ArrayValue field_names
---@return typed body
function typed:unwrap_record_elim() end
---@return boolean
---@return typed subject
---@return ArrayValue field_names
---@return typed body
function typed:as_record_elim() end
---@return boolean
function typed:is_enum_cons() end
---@return string constructor
---@return typed arg
function typed:unwrap_enum_cons() end
---@return boolean
---@return string constructor
---@return typed arg
function typed:as_enum_cons() end
---@return boolean
function typed:is_enum_elim() end
---@return typed subject
---@return typed mechanism
function typed:unwrap_enum_elim() end
---@return boolean
---@return typed subject
---@return typed mechanism
function typed:as_enum_elim() end
---@return boolean
function typed:is_enum_rec_elim() end
---@return typed subject
---@return typed mechanism
function typed:unwrap_enum_rec_elim() end
---@return boolean
---@return typed subject
---@return typed mechanism
function typed:as_enum_rec_elim() end
---@return boolean
function typed:is_enum_desc_cons() end
---@return MapValue variants
---@return typed rest
function typed:unwrap_enum_desc_cons() end
---@return boolean
---@return MapValue variants
---@return typed rest
function typed:as_enum_desc_cons() end
---@return boolean
function typed:is_enum_desc_type() end
---@return typed univ
function typed:unwrap_enum_desc_type() end
---@return boolean
---@return typed univ
function typed:as_enum_desc_type() end
---@return boolean
function typed:is_enum_type() end
---@return typed desc
function typed:unwrap_enum_type() end
---@return boolean
---@return typed desc
function typed:as_enum_type() end
---@return boolean
function typed:is_enum_case() end
---@return typed target
---@return MapValue variants
---@return typed default
function typed:unwrap_enum_case() end
---@return boolean
---@return typed target
---@return MapValue variants
---@return typed default
function typed:as_enum_case() end
---@return boolean
function typed:is_enum_absurd() end
---@return typed target
---@return string debug
function typed:unwrap_enum_absurd() end
---@return boolean
---@return typed target
---@return string debug
function typed:as_enum_absurd() end
---@return boolean
function typed:is_object_cons() end
---@return MapValue methods
function typed:unwrap_object_cons() end
---@return boolean
---@return MapValue methods
function typed:as_object_cons() end
---@return boolean
function typed:is_object_corec_cons() end
---@return MapValue methods
function typed:unwrap_object_corec_cons() end
---@return boolean
---@return MapValue methods
function typed:as_object_corec_cons() end
---@return boolean
function typed:is_object_elim() end
---@return typed subject
---@return typed mechanism
function typed:unwrap_object_elim() end
---@return boolean
---@return typed subject
---@return typed mechanism
function typed:as_object_elim() end
---@return boolean
function typed:is_operative_cons() end
---@return typed userdata
function typed:unwrap_operative_cons() end
---@return boolean
---@return typed userdata
function typed:as_operative_cons() end
---@return boolean
function typed:is_operative_type_cons() end
---@return typed handler
---@return typed userdata_type
function typed:unwrap_operative_type_cons() end
---@return boolean
---@return typed handler
---@return typed userdata_type
function typed:as_operative_type_cons() end
---@return boolean
function typed:is_host_tuple_cons() end
---@return ArrayValue elements
function typed:unwrap_host_tuple_cons() end
---@return boolean
---@return ArrayValue elements
function typed:as_host_tuple_cons() end
---@return boolean
function typed:is_host_user_defined_type_cons() end
---@return { name: string } id
---@return ArrayValue family_args
function typed:unwrap_host_user_defined_type_cons() end
---@return boolean
---@return { name: string } id
---@return ArrayValue family_args
function typed:as_host_user_defined_type_cons() end
---@return boolean
function typed:is_host_tuple_type() end
---@return typed desc
function typed:unwrap_host_tuple_type() end
---@return boolean
---@return typed desc
function typed:as_host_tuple_type() end
---@return boolean
function typed:is_host_function_type() end
---@return typed param_type
---@return typed result_type
---@return typed result_info
function typed:unwrap_host_function_type() end
---@return boolean
---@return typed param_type
---@return typed result_type
---@return typed result_info
function typed:as_host_function_type() end
---@return boolean
function typed:is_host_wrapped_type() end
---@return typed type
function typed:unwrap_host_wrapped_type() end
---@return boolean
---@return typed type
function typed:as_host_wrapped_type() end
---@return boolean
function typed:is_host_unstrict_wrapped_type() end
---@return typed type
function typed:unwrap_host_unstrict_wrapped_type() end
---@return boolean
---@return typed type
function typed:as_host_unstrict_wrapped_type() end
---@return boolean
function typed:is_host_wrap() end
---@return typed content
function typed:unwrap_host_wrap() end
---@return boolean
---@return typed content
function typed:as_host_wrap() end
---@return boolean
function typed:is_host_unwrap() end
---@return typed container
function typed:unwrap_host_unwrap() end
---@return boolean
---@return typed container
function typed:as_host_unwrap() end
---@return boolean
function typed:is_host_unstrict_wrap() end
---@return typed content
function typed:unwrap_host_unstrict_wrap() end
---@return boolean
---@return typed content
function typed:as_host_unstrict_wrap() end
---@return boolean
function typed:is_host_unstrict_unwrap() end
---@return typed container
function typed:unwrap_host_unstrict_unwrap() end
---@return boolean
---@return typed container
function typed:as_host_unstrict_unwrap() end
---@return boolean
function typed:is_host_user_defined_type() end
---@return { name: string } id
---@return ArrayValue family_args
function typed:unwrap_host_user_defined_type() end
---@return boolean
---@return { name: string } id
---@return ArrayValue family_args
function typed:as_host_user_defined_type() end
---@return boolean
function typed:is_host_if() end
---@return typed subject
---@return typed consequent
---@return typed alternate
function typed:unwrap_host_if() end
---@return boolean
---@return typed subject
---@return typed consequent
---@return typed alternate
function typed:as_host_if() end
---@return boolean
function typed:is_host_intrinsic() end
---@return typed source
---@return Anchor start_anchor
---@return Anchor end_anchor
function typed:unwrap_host_intrinsic() end
---@return boolean
---@return typed source
---@return Anchor start_anchor
---@return Anchor end_anchor
function typed:as_host_intrinsic() end
---@return boolean
function typed:is_range() end
---@return ArrayValue lower_bounds
---@return ArrayValue upper_bounds
---@return typed relation
function typed:unwrap_range() end
---@return boolean
---@return ArrayValue lower_bounds
---@return ArrayValue upper_bounds
---@return typed relation
function typed:as_range() end
---@return boolean
function typed:is_singleton() end
---@return typed supertype
---@return value value
function typed:unwrap_singleton() end
---@return boolean
---@return typed supertype
---@return value value
function typed:as_singleton() end
---@return boolean
function typed:is_program_sequence() end
---@return typed first
---@return typed continue
function typed:unwrap_program_sequence() end
---@return boolean
---@return typed first
---@return typed continue
function typed:as_program_sequence() end
---@return boolean
function typed:is_program_end() end
---@return typed result
function typed:unwrap_program_end() end
---@return boolean
---@return typed result
function typed:as_program_end() end
---@return boolean
function typed:is_program_invoke() end
---@return typed effect_tag
---@return typed effect_arg
function typed:unwrap_program_invoke() end
---@return boolean
---@return typed effect_tag
---@return typed effect_arg
function typed:as_program_invoke() end
---@return boolean
function typed:is_effect_type() end
---@return ArrayValue components
---@return typed base
function typed:unwrap_effect_type() end
---@return boolean
---@return ArrayValue components
---@return typed base
function typed:as_effect_type() end
---@return boolean
function typed:is_effect_row() end
---@return ArrayValue elems
---@return typed rest
function typed:unwrap_effect_row() end
---@return boolean
---@return ArrayValue elems
---@return typed rest
function typed:as_effect_row() end
---@return boolean
function typed:is_effect_row_resolve() end
---@return SetValue elems
---@return typed rest
function typed:unwrap_effect_row_resolve() end
---@return boolean
---@return SetValue elems
---@return typed rest
function typed:as_effect_row_resolve() end
---@return boolean
function typed:is_program_type() end
---@return typed effect_type
---@return typed result_type
function typed:unwrap_program_type() end
---@return boolean
---@return typed effect_type
---@return typed result_type
function typed:as_program_type() end
---@return boolean
function typed:is_srel_type() end
---@return typed target_type
function typed:unwrap_srel_type() end
---@return boolean
---@return typed target_type
function typed:as_srel_type() end
---@return boolean
function typed:is_variance_type() end
---@return typed target_type
function typed:unwrap_variance_type() end
---@return boolean
---@return typed target_type
function typed:as_variance_type() end
---@return boolean
function typed:is_variance_cons() end
---@return typed positive
---@return typed srel
function typed:unwrap_variance_cons() end
---@return boolean
---@return typed positive
---@return typed srel
function typed:as_variance_cons() end
---@return boolean
function typed:is_intersection_type() end
---@return typed left
---@return typed right
function typed:unwrap_intersection_type() end
---@return boolean
---@return typed left
---@return typed right
function typed:as_intersection_type() end
---@return boolean
function typed:is_union_type() end
---@return typed left
---@return typed right
function typed:unwrap_union_type() end
---@return boolean
---@return typed left
---@return typed right
function typed:as_union_type() end
---@return boolean
function typed:is_constrained_type() end
---@return ArrayValue constraints
---@return TypecheckingContext ctx
function typed:unwrap_constrained_type() end
---@return boolean
---@return ArrayValue constraints
---@return TypecheckingContext ctx
function typed:as_constrained_type() end

---@class (exact) typedType: EnumType
---@field define_enum fun(self: typedType, name: string, variants: Variants): typedType
---@field bound_variable fun(index: number, debug: any): typed
---@field literal fun(literal_value: value): typed
---@field lambda fun(param_name: string, body: typed, start_anchor: Anchor): typed
---@field pi fun(param_type: typed, param_info: typed, result_type: typed, result_info: typed): typed
---@field application fun(f: typed, arg: typed): typed
---@field let fun(name: string, expr: typed, body: typed): typed
---@field level_type typed
---@field level0 typed
---@field level_suc fun(previous_level: typed): typed
---@field level_max fun(level_a: typed, level_b: typed): typed
---@field star fun(level: number, depth: number): typed
---@field prop fun(level: number): typed
---@field tuple_cons fun(elements: ArrayValue): typed
---@field tuple_elim fun(names: ArrayValue, subject: typed, length: number, body: typed): typed
---@field tuple_element_access fun(subject: typed, index: number): typed
---@field tuple_type fun(desc: typed): typed
---@field tuple_desc_type fun(universe: typed): typed
---@field record_cons fun(fields: MapValue): typed
---@field record_extend fun(base: typed, fields: MapValue): typed
---@field record_elim fun(subject: typed, field_names: ArrayValue, body: typed): typed
---@field enum_cons fun(constructor: string, arg: typed): typed
---@field enum_elim fun(subject: typed, mechanism: typed): typed
---@field enum_rec_elim fun(subject: typed, mechanism: typed): typed
---@field enum_desc_cons fun(variants: MapValue, rest: typed): typed
---@field enum_desc_type fun(univ: typed): typed
---@field enum_type fun(desc: typed): typed
---@field enum_case fun(target: typed, variants: MapValue, default: typed): typed
---@field enum_absurd fun(target: typed, debug: string): typed
---@field object_cons fun(methods: MapValue): typed
---@field object_corec_cons fun(methods: MapValue): typed
---@field object_elim fun(subject: typed, mechanism: typed): typed
---@field operative_cons fun(userdata: typed): typed
---@field operative_type_cons fun(handler: typed, userdata_type: typed): typed
---@field host_tuple_cons fun(elements: ArrayValue): typed
---@field host_user_defined_type_cons fun(id: { name: string }, family_args: ArrayValue): typed
---@field host_tuple_type fun(desc: typed): typed
---@field host_function_type fun(param_type: typed, result_type: typed, result_info: typed): typed
---@field host_wrapped_type fun(type: typed): typed
---@field host_unstrict_wrapped_type fun(type: typed): typed
---@field host_wrap fun(content: typed): typed
---@field host_unwrap fun(container: typed): typed
---@field host_unstrict_wrap fun(content: typed): typed
---@field host_unstrict_unwrap fun(container: typed): typed
---@field host_user_defined_type fun(id: { name: string }, family_args: ArrayValue): typed
---@field host_if fun(subject: typed, consequent: typed, alternate: typed): typed
---@field host_intrinsic fun(source: typed, start_anchor: Anchor, end_anchor: Anchor): typed
---@field range fun(lower_bounds: ArrayValue, upper_bounds: ArrayValue, relation: typed): typed
---@field singleton fun(supertype: typed, value: value): typed
---@field program_sequence fun(first: typed, continue: typed): typed
---@field program_end fun(result: typed): typed
---@field program_invoke fun(effect_tag: typed, effect_arg: typed): typed
---@field effect_type fun(components: ArrayValue, base: typed): typed
---@field effect_row fun(elems: ArrayValue, rest: typed): typed
---@field effect_row_resolve fun(elems: SetValue, rest: typed): typed
---@field program_type fun(effect_type: typed, result_type: typed): typed
---@field srel_type fun(target_type: typed): typed
---@field variance_type fun(target_type: typed): typed
---@field variance_cons fun(positive: typed, srel: typed): typed
---@field intersection_type fun(left: typed, right: typed): typed
---@field union_type fun(left: typed, right: typed): typed
---@field constrained_type fun(constraints: ArrayValue, ctx: TypecheckingContext): typed
return {}
