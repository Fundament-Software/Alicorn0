local terms = require "terms"
local runtime_context = terms.runtime_context
local typechecking_context = terms.typechecking_context
local inferrable_term = terms.inferrable_term
local typed_term = terms.typed_term
local value = terms.value

local format = require "format"
local gen = require "terms-generators"
local map = gen.declare_map
local string_inferrable_map = map(gen.builtin_string, inferrable_term)
local string_typed_map = map(gen.builtin_string, typed_term)
local array = gen.declare_array
local inferrable_array = array(inferrable_term)
local typed_array = array(typed_term)
local value_array = array(value)
local usage_array = array(gen.builtin_number)
local string_array = array(gen.builtin_string)

local function tup_val(...)
	return value.tuple_value(value_array(...))
end
local function cons(...)
	return value.enum_value("cons", tup_val(...))
end
local empty = value.enum_value("empty", tup_val())

local evaluator = require "evaluator"
local const_combinator = evaluator.const_combinator
local infer = evaluator.infer
local evaluate = evaluator.evaluate

print("PART ONE!!!!!!!!!!")

local function eval_test(name, term)
	local initial_context = runtime_context()
	print("TEST: " .. name)
	print("initial")
	print(term:pretty_print(initial_context))
	local result = evaluate(term, initial_context)
	print("result")
	print(result:pretty_print())
	return result
end

local lit = typed_term.literal
local var = typed_term.bound_variable
local lam = typed_term.lambda
local app = typed_term.application

local num = value.number
local n42 = lit(num(42))
local n69 = lit(num(69))
local n420 = lit(num(420))
local n621 = lit(num(621))
local n926 = lit(num(926))
local n1337 = lit(num(1337))

-- var(1) refers to the outermost bound variable, 2 next outermost, etc
-- as opposed to de bruijn indices, where 1 refers to the innermost (nearest) binding, etc
local id = lam("x", var(1)) -- \x -> x
local const = lam("x", lam("y", var(1))) -- \x -> \y -> x
-- in de bruijn indices, these would be lam("x", var(1)) and lam("x", lam("y", var(2))) respectively

local result

local apply_id_with_42 = app(id, n42)
result = eval_test("apply_id_with_42", apply_id_with_42)
assert(result:is_number() and result:unwrap_number() == 42)

local apply_closure_with_capture = app(app(const, n69), n1337)
result = eval_test("apply_closure_with_capture", apply_closure_with_capture)
assert(result:is_number() and result:unwrap_number() == 69)

local apply_partial_closure_with_capture = app(const, n69)
result = eval_test("apply_partial_closure_with_capture", apply_partial_closure_with_capture)

print("PART TWO!!!!!!!!!!")

local function infer_and_eval(name, inf)
	local initial_context = runtime_context()
	local initial_typechecking_context = typechecking_context()
	print("TEST: " .. name)
	print("initial")
	print(inf:pretty_print(initial_typechecking_context))
	local result_type, result_usages, result_term = infer(inf, initial_typechecking_context)
	print("result_type")
	print(result_type:pretty_print())
	print("result_usages")
	print(result_usages:pretty_print())
	print("result_term")
	print(result_term:pretty_print(initial_context))
	local result = evaluate(result_term, initial_context)
	print("result")
	print(result:pretty_print())
	return result
end

local function inf_t(t)
	return inferrable_term.typed(value.star(0, 0), usage_array(), lit(t))
end
local function inf_typ(t, typ)
	return inferrable_term.typed(t, usage_array(), typ)
end
local inf_var = inferrable_term.bound_variable

local function host_lit(x)
	return lit(value.host_value(x))
end

local inf_app = inferrable_term.application

local t_num = value.number_type
local i42 = inf_typ(t_num, n42)
local i69 = inf_typ(t_num, n69)
local i420 = inf_typ(t_num, n420)
local i621 = inf_typ(t_num, n621)
local i926 = inf_typ(t_num, n926)
local i1337 = inf_typ(t_num, n1337)

local chk_inf = terms.checkable_term.inferrable

local literal_purity_pure = chk_inf(inf_typ(terms.host_purity_type, host_lit(terms.purity.pure)))
local function inf_lam(n, t, b)
	return inferrable_term.annotated_lambda(
		n,
		inf_t(t),
		b,
		format.create_anchor(107, 2, "test-eval.lua"),
		terms.visibility.explicit,
		literal_purity_pure
	)
end

local c42 = chk_inf(i42)
local c69 = chk_inf(i69)
local c1337 = chk_inf(i1337)

local inf_id = inf_lam("x", t_num, inf_var(1))
local inf_const = inf_lam("val", t_num, inf_lam("ignored", t_num, inf_var(1)))

local apply_inf_id_with_42 = inf_app(inf_id, c42)
infer_and_eval("apply_inf_id_with_42", apply_inf_id_with_42)

local apply_inf_closure_with_capture = inf_app(inf_app(inf_const, c69), c1337)
infer_and_eval("apply_inf_closure_with_capture", apply_inf_closure_with_capture)

print("PART THREE!!!!!!!!")

local function inf_tup(...)
	return inferrable_term.tuple_cons(inferrable_array(...))
end
local inf_tupelim = inferrable_term.tuple_elim
local tuple_of_69_420 = inf_tup(i69, i420)
local name_tuple_of_69_420 = string_array("i69", "i420")
infer_and_eval("tuple_of_69_420", tuple_of_69_420)

local inf_swap = inf_tup(inf_var(2), inf_var(1))
local swap_69_420 = inf_tupelim(name_tuple_of_69_420, tuple_of_69_420, inf_swap)
infer_and_eval("swap_69_420", swap_69_420)

print("PART FOUR!!!!!!!!!")

local host_add = host_lit(function(left, right)
	return left + right
end)
local function host_tup(...)
	return typed_term.host_tuple_cons(typed_array(...))
end

local h69 = host_lit(69)
local h420 = host_lit(420)
local h621 = host_lit(621)
local h926 = host_lit(926)

local host_add_69_420 = app(host_add, host_tup(h69, h420))
eval_test("host_add_69_420", host_add_69_420)

local function inf_host_tup(...)
	return inferrable_term.host_tuple_cons(inferrable_array(...))
end

local t_host_num = value.host_number_type
local ih69 = inf_typ(t_host_num, h69)
local ih420 = inf_typ(t_host_num, h420)
local ih621 = inf_typ(t_host_num, h621)
local ih926 = inf_typ(t_host_num, h926)

local tuple_of_621_420 = inf_host_tup(ih621, ih420)
local name_tuple_of_621_420 = string_array("ih621", "ih420")
infer_and_eval("tuple_of_621_420", tuple_of_621_420)

local inf_host_swap = inf_host_tup(inf_var(2), inf_var(1))
local swap_host_621_420 = inf_tupelim(name_tuple_of_621_420, tuple_of_621_420, inf_host_swap)
infer_and_eval("swap_host_621_420", swap_host_621_420)

print("PART FIVE!!!!!!!!!")

-- create host tuple
-- call host function
-- use tuple elim to extract results and repack with another host value
-- call another host function

local hostextractrepack = host_tup(var(1), host_lit(-1))

local input = host_tup(host_lit(2)) -- -> (2)
local returns_input_and_3 = host_lit(function(a)
	return a, 3
end) -- returns_input_and_3(2) -> (2, 3)
local result = app(host_add, app(returns_input_and_3, input)) -- add(2, 3) -> (5)
local t = typed_term.tuple_elim(string_array("result"), result, 1, hostextractrepack) -- (5) -> (5, -1)
local result_2 = app(host_add, t) -- add(5, -1) -> 4
local result_3 = typed_term.tuple_elim(string_array("result_2"), result_2, 1, var(1))
eval_test("repacking_tuples", result_3)

-- local fmt = require 'format-adapter'
-- local user_defined_host_a_id = { name = "syntax" }
-- local user_defined_host_a_cons = inferrable_term.host_user_defined_type_cons(user_defined_host_a_id, inferrable_array())
-- local value_user_defined_host_a = infer_and_eval("syn_host_cons", user_defined_host_a_cons)

-- local host_fmt_read = host_lit(function(str) return fmt.read(str, "inline") end)
-- local infer_host_fmt_read = inferrable_term.typed(value_user_defined_host_a, usage_array(), typed_term.literal(value.host_value(host_fmt_read)))
-- infer_and_eval("user_defined_host_syntax_cons", inf_app(infer_host_fmt_read, inferrable_term.typed(value.host_string_type, usage_array(), host_lit("+ 2 3"))))

print("PART SIX!!!!!!!!!!")

local cupnum = const_combinator(t_host_num)
local tuple_decl = value.host_tuple_type(cons(cons(empty, cupnum), cupnum))
local mogrify = host_lit(function(left, right)
	return left + right, left - right
end)
local inf_mogrify = inf_typ(
	value.host_function_type(
		tuple_decl,
		const_combinator(tuple_decl),
		value.result_info(terms.result_info(terms.purity.pure))
	),
	mogrify
)
local apply_mogrify_with_621_420 = inf_app(inf_mogrify, chk_inf(tuple_of_621_420))
infer_and_eval("apply_mogrify_with_621_420", apply_mogrify_with_621_420)

print("PART SEVEN!!!!!!!!")
local function desc2map(t, map_desc)
	local map = t()
	local odd = true
	local key
	for _, v in ipairs(map_desc) do
		if odd then
			key = v
		else
			map:set(key, v)
		end
		odd = not odd
	end
	return map
end
local function inf_rec(map_desc)
	local map = desc2map(string_inferrable_map, map_desc)
	return inferrable_term.record_cons(map)
end
local inf_recelim = inferrable_term.record_elim

print("TODO: Re-enable tests part 7 and 8 after we fix record types.")
print("Success!")

--[[local record_621_926 = inf_rec({ "foo", i621, "bar", i926 })
infer_and_eval("record_621_926", record_621_926)

local record_swap = inf_rec({ "baz", inf_var(2), "quux", inf_var(1) })
local swap_621_926 = inf_recelim(record_621_926, string_array("foo", "bar"), record_swap)
infer_and_eval("swap_621_926", swap_621_926)

local record_host_621_926 = inf_rec({ "foo", ih621, "bar", ih926 })
local tuple_conv = inf_host_tup(inf_var(1), inf_var(2))
local record_conv = inf_rec({ "sum", inf_var(1), "difference", inf_var(2) })
local megamogrify = inf_tupelim(
	string_array("inf_app_mogrify", "record_conv"),
	inf_app(
		inf_mogrify,
		chk_inf(inf_recelim(record_host_621_926, string_array("foo", "bar"), tuple_conv))
	),
	record_conv
)
infer_and_eval("megamogrify", megamogrify)

print("PART EIGHT!!!!!!!!")

local enum_foo_host_69 = typed_term.enum_cons("foo", h69)
local host_add_1 = host_lit(function(x)
	return x + 1
end)
local host_subtract_1 = host_lit(function(x)
	return x - 1
end)
local hosttupify = lam("f", app(var(2), host_tup(var(1))))
local untupify = var(1)
local add_1 = app(hosttupify, host_add_1)
local subtract_1 = app(hosttupify, host_subtract_1)
local obj_foo_bar = typed_term.object_cons(desc2map(string_typed_map, { "foo", add_1, "bar", subtract_1 }))
local typed_enum_elim = typed_term.tuple_elim(
	string_array("result"),
	typed_term.enum_elim(enum_foo_host_69, obj_foo_bar),
	1,
	untupify
)
eval_test("typed_enum_elim", typed_enum_elim)

local typed_object_elim =
	typed_term.tuple_elim(string_array("result"), typed_term.object_elim(obj_foo_bar, enum_foo_host_69), 1, untupify)
eval_test("typed_object_elim", typed_object_elim)]]
