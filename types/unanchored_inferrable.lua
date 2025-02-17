-- THIS FILE AUTOGENERATED BY terms-gen-meta.lua
---@meta "types.unanchored_inferrable"

---@class (exact) unanchored_inferrable: EnumValue
unanchored_inferrable = {}

---@return boolean
function unanchored_inferrable:is_bound_variable() end
---@return number index
---@return spanned_name debug
function unanchored_inferrable:unwrap_bound_variable() end
---@return boolean
---@return number index
---@return spanned_name debug
function unanchored_inferrable:as_bound_variable() end
---@return boolean
function unanchored_inferrable:is_typed() end
---@return typed type
---@return ArrayValue<number> usage_counts
---@return typed typed_term
function unanchored_inferrable:unwrap_typed() end
---@return boolean
---@return typed type
---@return ArrayValue<number> usage_counts
---@return typed typed_term
function unanchored_inferrable:as_typed() end
---@return boolean
function unanchored_inferrable:is_annotated_lambda() end
---@return string param_name
---@return anchored_inferrable param_annotation
---@return anchored_inferrable body
---@return Anchor start_anchor
---@return visibility visible
---@return checkable pure
function unanchored_inferrable:unwrap_annotated_lambda() end
---@return boolean
---@return string param_name
---@return anchored_inferrable param_annotation
---@return anchored_inferrable body
---@return Anchor start_anchor
---@return visibility visible
---@return checkable pure
function unanchored_inferrable:as_annotated_lambda() end
---@return boolean
function unanchored_inferrable:is_pi() end
---@return anchored_inferrable param_type
---@return checkable param_info
---@return anchored_inferrable result_type
---@return checkable result_info
function unanchored_inferrable:unwrap_pi() end
---@return boolean
---@return anchored_inferrable param_type
---@return checkable param_info
---@return anchored_inferrable result_type
---@return checkable result_info
function unanchored_inferrable:as_pi() end
---@return boolean
function unanchored_inferrable:is_application() end
---@return anchored_inferrable f
---@return checkable arg
function unanchored_inferrable:unwrap_application() end
---@return boolean
---@return anchored_inferrable f
---@return checkable arg
function unanchored_inferrable:as_application() end
---@return boolean
function unanchored_inferrable:is_tuple_cons() end
---@return ArrayValue<anchored_inferrable> elements
---@return ArrayValue<spanned_name> debug
function unanchored_inferrable:unwrap_tuple_cons() end
---@return boolean
---@return ArrayValue<anchored_inferrable> elements
---@return ArrayValue<spanned_name> debug
function unanchored_inferrable:as_tuple_cons() end
---@return boolean
function unanchored_inferrable:is_tuple_elim() end
---@return ArrayValue<string> names
---@return ArrayValue<spanned_name> debug
---@return anchored_inferrable subject
---@return anchored_inferrable body
function unanchored_inferrable:unwrap_tuple_elim() end
---@return boolean
---@return ArrayValue<string> names
---@return ArrayValue<spanned_name> debug
---@return anchored_inferrable subject
---@return anchored_inferrable body
function unanchored_inferrable:as_tuple_elim() end
---@return boolean
function unanchored_inferrable:is_tuple_type() end
---@return anchored_inferrable desc
function unanchored_inferrable:unwrap_tuple_type() end
---@return boolean
---@return anchored_inferrable desc
function unanchored_inferrable:as_tuple_type() end
---@return boolean
function unanchored_inferrable:is_record_cons() end
---@return MapValue<string, anchored_inferrable> fields
function unanchored_inferrable:unwrap_record_cons() end
---@return boolean
---@return MapValue<string, anchored_inferrable> fields
function unanchored_inferrable:as_record_cons() end
---@return boolean
function unanchored_inferrable:is_record_elim() end
---@return anchored_inferrable subject
---@return ArrayValue<string> field_names
---@return anchored_inferrable body
function unanchored_inferrable:unwrap_record_elim() end
---@return boolean
---@return anchored_inferrable subject
---@return ArrayValue<string> field_names
---@return anchored_inferrable body
function unanchored_inferrable:as_record_elim() end
---@return boolean
function unanchored_inferrable:is_enum_cons() end
---@return string constructor
---@return anchored_inferrable arg
function unanchored_inferrable:unwrap_enum_cons() end
---@return boolean
---@return string constructor
---@return anchored_inferrable arg
function unanchored_inferrable:as_enum_cons() end
---@return boolean
function unanchored_inferrable:is_enum_desc_cons() end
---@return MapValue<string, anchored_inferrable> variants
---@return anchored_inferrable rest
function unanchored_inferrable:unwrap_enum_desc_cons() end
---@return boolean
---@return MapValue<string, anchored_inferrable> variants
---@return anchored_inferrable rest
function unanchored_inferrable:as_enum_desc_cons() end
---@return boolean
function unanchored_inferrable:is_enum_elim() end
---@return anchored_inferrable subject
---@return anchored_inferrable mechanism
function unanchored_inferrable:unwrap_enum_elim() end
---@return boolean
---@return anchored_inferrable subject
---@return anchored_inferrable mechanism
function unanchored_inferrable:as_enum_elim() end
---@return boolean
function unanchored_inferrable:is_enum_type() end
---@return anchored_inferrable desc
function unanchored_inferrable:unwrap_enum_type() end
---@return boolean
---@return anchored_inferrable desc
function unanchored_inferrable:as_enum_type() end
---@return boolean
function unanchored_inferrable:is_enum_case() end
---@return anchored_inferrable target
---@return MapValue<string, anchored_inferrable> variants
---@return MapValue<string, spanned_name> variant_debug
function unanchored_inferrable:unwrap_enum_case() end
---@return boolean
---@return anchored_inferrable target
---@return MapValue<string, anchored_inferrable> variants
---@return MapValue<string, spanned_name> variant_debug
function unanchored_inferrable:as_enum_case() end
---@return boolean
function unanchored_inferrable:is_enum_absurd() end
---@return anchored_inferrable target
---@return string debug
function unanchored_inferrable:unwrap_enum_absurd() end
---@return boolean
---@return anchored_inferrable target
---@return string debug
function unanchored_inferrable:as_enum_absurd() end
---@return boolean
function unanchored_inferrable:is_object_cons() end
---@return MapValue<string, anchored_inferrable> methods
function unanchored_inferrable:unwrap_object_cons() end
---@return boolean
---@return MapValue<string, anchored_inferrable> methods
function unanchored_inferrable:as_object_cons() end
---@return boolean
function unanchored_inferrable:is_object_elim() end
---@return anchored_inferrable subject
---@return anchored_inferrable mechanism
function unanchored_inferrable:unwrap_object_elim() end
---@return boolean
---@return anchored_inferrable subject
---@return anchored_inferrable mechanism
function unanchored_inferrable:as_object_elim() end
---@return boolean
function unanchored_inferrable:is_let() end
---@return string name
---@return spanned_name debug
---@return anchored_inferrable expr
---@return anchored_inferrable body
function unanchored_inferrable:unwrap_let() end
---@return boolean
---@return string name
---@return spanned_name debug
---@return anchored_inferrable expr
---@return anchored_inferrable body
function unanchored_inferrable:as_let() end
---@return boolean
function unanchored_inferrable:is_operative_cons() end
---@return anchored_inferrable operative_type
---@return anchored_inferrable userdata
function unanchored_inferrable:unwrap_operative_cons() end
---@return boolean
---@return anchored_inferrable operative_type
---@return anchored_inferrable userdata
function unanchored_inferrable:as_operative_cons() end
---@return boolean
function unanchored_inferrable:is_operative_type_cons() end
---@return anchored_inferrable userdata_type
---@return checkable handler
function unanchored_inferrable:unwrap_operative_type_cons() end
---@return boolean
---@return anchored_inferrable userdata_type
---@return checkable handler
function unanchored_inferrable:as_operative_type_cons() end
---@return boolean
function unanchored_inferrable:is_level_type() end
---@return nil
function unanchored_inferrable:unwrap_level_type() end
---@return boolean
function unanchored_inferrable:as_level_type() end
---@return boolean
function unanchored_inferrable:is_level0() end
---@return nil
function unanchored_inferrable:unwrap_level0() end
---@return boolean
function unanchored_inferrable:as_level0() end
---@return boolean
function unanchored_inferrable:is_level_suc() end
---@return anchored_inferrable previous_level
function unanchored_inferrable:unwrap_level_suc() end
---@return boolean
---@return anchored_inferrable previous_level
function unanchored_inferrable:as_level_suc() end
---@return boolean
function unanchored_inferrable:is_level_max() end
---@return anchored_inferrable level_a
---@return anchored_inferrable level_b
function unanchored_inferrable:unwrap_level_max() end
---@return boolean
---@return anchored_inferrable level_a
---@return anchored_inferrable level_b
function unanchored_inferrable:as_level_max() end
---@return boolean
function unanchored_inferrable:is_annotated() end
---@return checkable annotated_term
---@return anchored_inferrable annotated_type
function unanchored_inferrable:unwrap_annotated() end
---@return boolean
---@return checkable annotated_term
---@return anchored_inferrable annotated_type
function unanchored_inferrable:as_annotated() end
---@return boolean
function unanchored_inferrable:is_host_tuple_cons() end
---@return ArrayValue<anchored_inferrable> elements
---@return ArrayValue<spanned_name> debug
function unanchored_inferrable:unwrap_host_tuple_cons() end
---@return boolean
---@return ArrayValue<anchored_inferrable> elements
---@return ArrayValue<spanned_name> debug
function unanchored_inferrable:as_host_tuple_cons() end
---@return boolean
function unanchored_inferrable:is_host_user_defined_type_cons() end
---@return { name: string } id
---@return ArrayValue<anchored_inferrable> family_args
function unanchored_inferrable:unwrap_host_user_defined_type_cons() end
---@return boolean
---@return { name: string } id
---@return ArrayValue<anchored_inferrable> family_args
function unanchored_inferrable:as_host_user_defined_type_cons() end
---@return boolean
function unanchored_inferrable:is_host_tuple_type() end
---@return anchored_inferrable desc
function unanchored_inferrable:unwrap_host_tuple_type() end
---@return boolean
---@return anchored_inferrable desc
function unanchored_inferrable:as_host_tuple_type() end
---@return boolean
function unanchored_inferrable:is_host_function_type() end
---@return anchored_inferrable param_type
---@return anchored_inferrable result_type
---@return checkable result_info
function unanchored_inferrable:unwrap_host_function_type() end
---@return boolean
---@return anchored_inferrable param_type
---@return anchored_inferrable result_type
---@return checkable result_info
function unanchored_inferrable:as_host_function_type() end
---@return boolean
function unanchored_inferrable:is_host_wrapped_type() end
---@return anchored_inferrable type
function unanchored_inferrable:unwrap_host_wrapped_type() end
---@return boolean
---@return anchored_inferrable type
function unanchored_inferrable:as_host_wrapped_type() end
---@return boolean
function unanchored_inferrable:is_host_unstrict_wrapped_type() end
---@return anchored_inferrable type
function unanchored_inferrable:unwrap_host_unstrict_wrapped_type() end
---@return boolean
---@return anchored_inferrable type
function unanchored_inferrable:as_host_unstrict_wrapped_type() end
---@return boolean
function unanchored_inferrable:is_host_wrap() end
---@return anchored_inferrable content
function unanchored_inferrable:unwrap_host_wrap() end
---@return boolean
---@return anchored_inferrable content
function unanchored_inferrable:as_host_wrap() end
---@return boolean
function unanchored_inferrable:is_host_unstrict_wrap() end
---@return anchored_inferrable content
function unanchored_inferrable:unwrap_host_unstrict_wrap() end
---@return boolean
---@return anchored_inferrable content
function unanchored_inferrable:as_host_unstrict_wrap() end
---@return boolean
function unanchored_inferrable:is_host_unwrap() end
---@return anchored_inferrable container
function unanchored_inferrable:unwrap_host_unwrap() end
---@return boolean
---@return anchored_inferrable container
function unanchored_inferrable:as_host_unwrap() end
---@return boolean
function unanchored_inferrable:is_host_unstrict_unwrap() end
---@return anchored_inferrable container
function unanchored_inferrable:unwrap_host_unstrict_unwrap() end
---@return boolean
---@return anchored_inferrable container
function unanchored_inferrable:as_host_unstrict_unwrap() end
---@return boolean
function unanchored_inferrable:is_host_if() end
---@return checkable subject
---@return anchored_inferrable consequent
---@return anchored_inferrable alternate
function unanchored_inferrable:unwrap_host_if() end
---@return boolean
---@return checkable subject
---@return anchored_inferrable consequent
---@return anchored_inferrable alternate
function unanchored_inferrable:as_host_if() end
---@return boolean
function unanchored_inferrable:is_host_intrinsic() end
---@return checkable source
---@return anchored_inferrable type
---@return Anchor start_anchor
function unanchored_inferrable:unwrap_host_intrinsic() end
---@return boolean
---@return checkable source
---@return anchored_inferrable type
---@return Anchor start_anchor
function unanchored_inferrable:as_host_intrinsic() end
---@return boolean
function unanchored_inferrable:is_program_sequence() end
---@return anchored_inferrable first
---@return Anchor start_anchor
---@return anchored_inferrable continue
---@return spanned_name debug_info
function unanchored_inferrable:unwrap_program_sequence() end
---@return boolean
---@return anchored_inferrable first
---@return Anchor start_anchor
---@return anchored_inferrable continue
---@return spanned_name debug_info
function unanchored_inferrable:as_program_sequence() end
---@return boolean
function unanchored_inferrable:is_program_end() end
---@return anchored_inferrable result
function unanchored_inferrable:unwrap_program_end() end
---@return boolean
---@return anchored_inferrable result
function unanchored_inferrable:as_program_end() end
---@return boolean
function unanchored_inferrable:is_program_type() end
---@return anchored_inferrable effect_type
---@return anchored_inferrable result_type
function unanchored_inferrable:unwrap_program_type() end
---@return boolean
---@return anchored_inferrable effect_type
---@return anchored_inferrable result_type
function unanchored_inferrable:as_program_type() end

---@class (exact) unanchored_inferrableType: EnumType
---@field define_enum fun(self: unanchored_inferrableType, name: string, variants: Variants): unanchored_inferrableType
---@field bound_variable fun(index: number, debug: spanned_name): unanchored_inferrable
---@field typed fun(type: typed, usage_counts: ArrayValue<number>, typed_term: typed): unanchored_inferrable
---@field annotated_lambda fun(param_name: string, param_annotation: anchored_inferrable, body: anchored_inferrable, start_anchor: Anchor, visible: visibility, pure: checkable): unanchored_inferrable
---@field pi fun(param_type: anchored_inferrable, param_info: checkable, result_type: anchored_inferrable, result_info: checkable): unanchored_inferrable
---@field application fun(f: anchored_inferrable, arg: checkable): unanchored_inferrable
---@field tuple_cons fun(elements: ArrayValue<anchored_inferrable>, debug: ArrayValue<spanned_name>): unanchored_inferrable
---@field tuple_elim fun(names: ArrayValue<string>, debug: ArrayValue<spanned_name>, subject: anchored_inferrable, body: anchored_inferrable): unanchored_inferrable
---@field tuple_type fun(desc: anchored_inferrable): unanchored_inferrable
---@field record_cons fun(fields: MapValue<string, anchored_inferrable>): unanchored_inferrable
---@field record_elim fun(subject: anchored_inferrable, field_names: ArrayValue<string>, body: anchored_inferrable): unanchored_inferrable
---@field enum_cons fun(constructor: string, arg: anchored_inferrable): unanchored_inferrable
---@field enum_desc_cons fun(variants: MapValue<string, anchored_inferrable>, rest: anchored_inferrable): unanchored_inferrable
---@field enum_elim fun(subject: anchored_inferrable, mechanism: anchored_inferrable): unanchored_inferrable
---@field enum_type fun(desc: anchored_inferrable): unanchored_inferrable
---@field enum_case fun(target: anchored_inferrable, variants: MapValue<string, anchored_inferrable>, variant_debug: MapValue<string, spanned_name>): unanchored_inferrable
---@field enum_absurd fun(target: anchored_inferrable, debug: string): unanchored_inferrable
---@field object_cons fun(methods: MapValue<string, anchored_inferrable>): unanchored_inferrable
---@field object_elim fun(subject: anchored_inferrable, mechanism: anchored_inferrable): unanchored_inferrable
---@field let fun(name: string, debug: spanned_name, expr: anchored_inferrable, body: anchored_inferrable): unanchored_inferrable
---@field operative_cons fun(operative_type: anchored_inferrable, userdata: anchored_inferrable): unanchored_inferrable
---@field operative_type_cons fun(userdata_type: anchored_inferrable, handler: checkable): unanchored_inferrable
---@field level_type unanchored_inferrable
---@field level0 unanchored_inferrable
---@field level_suc fun(previous_level: anchored_inferrable): unanchored_inferrable
---@field level_max fun(level_a: anchored_inferrable, level_b: anchored_inferrable): unanchored_inferrable
---@field annotated fun(annotated_term: checkable, annotated_type: anchored_inferrable): unanchored_inferrable
---@field host_tuple_cons fun(elements: ArrayValue<anchored_inferrable>, debug: ArrayValue<spanned_name>): unanchored_inferrable
---@field host_user_defined_type_cons fun(id: { name: string }, family_args: ArrayValue<anchored_inferrable>): unanchored_inferrable
---@field host_tuple_type fun(desc: anchored_inferrable): unanchored_inferrable
---@field host_function_type fun(param_type: anchored_inferrable, result_type: anchored_inferrable, result_info: checkable): unanchored_inferrable
---@field host_wrapped_type fun(type: anchored_inferrable): unanchored_inferrable
---@field host_unstrict_wrapped_type fun(type: anchored_inferrable): unanchored_inferrable
---@field host_wrap fun(content: anchored_inferrable): unanchored_inferrable
---@field host_unstrict_wrap fun(content: anchored_inferrable): unanchored_inferrable
---@field host_unwrap fun(container: anchored_inferrable): unanchored_inferrable
---@field host_unstrict_unwrap fun(container: anchored_inferrable): unanchored_inferrable
---@field host_if fun(subject: checkable, consequent: anchored_inferrable, alternate: anchored_inferrable): unanchored_inferrable
---@field host_intrinsic fun(source: checkable, type: anchored_inferrable, start_anchor: Anchor): unanchored_inferrable
---@field program_sequence fun(first: anchored_inferrable, start_anchor: Anchor, continue: anchored_inferrable, debug_info: spanned_name): unanchored_inferrable
---@field program_end fun(result: anchored_inferrable): unanchored_inferrable
---@field program_type fun(effect_type: anchored_inferrable, result_type: anchored_inferrable): unanchored_inferrable
return {}
