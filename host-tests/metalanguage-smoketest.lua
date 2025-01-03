local metalanguage = require "metalanguage"
local exprs = require "alicorn-expressions"
local format = require "format-adapter"

local trie = require "lazy-prefix-tree"
local environment = require "environment"

local terms = require "terms"
local terms_gen = require "terms-generators"
local number = terms.value.host_number_type
local unit = terms.inferrable_term.tuple_cons(terms_gen.declare_array(terms.inferrable_term)())

-- for k, v in pairs(lang) do print(k, v) end

local symbol, value, list = metalanguage.symbol, metalanguage.value, metalanguage.list

--[[
local code =
  list(
    symbol "+",
    value(1),
    value(2)
  )
--]]

local src = "do (val x = 6) (+ x 3)"
local code = format.read(src, "inline")

local function do_block_pair_handler(env, a, b)
	local ok, val, newenv = a:match({
		exprs.inferred_expression(metalanguage.accept_handler, env),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return false, val
	end
	--print("do block pair handler", ok, val, newenv, b)
	return true, true, val, newenv, b
end

local function do_block_nil_handler(env)
	return true, false, nil, env, nil
end

local function do_block(syntax, env)
	local res = nil
	local ok, ispair, val, newenv, tail = true, true, nil, env, nil
	local shadowed
	shadowed, env = env:enter_block(terms.block_purity.pure)
	while ok and ispair do
		ok, ispair, val, newenv, tail = syntax:match({
			metalanguage.ispair(do_block_pair_handler),
			metalanguage.isnil(do_block_nil_handler),
		}, metalanguage.failure_handler, newenv)
		--print("do block", ok, ispair, val, newenv, tail)
		if not ok then
			return false, ispair
		end
		if ispair then
			res = val
			syntax = tail
		end
	end
	env = newenv
	env, res = env:exit_block(res, shadowed)
	return true, res, env
end

local function val_bind(syntax, env)
	local ok, symbol, val = syntax:match({
		metalanguage.listmatch(
			metalanguage.accept_handler,
			metalanguage.issymbol(metalanguage.accept_handler),
			metalanguage.symbol_exact(metalanguage.accept_handler, "="),
			exprs.inferred_expression(metalanguage.accept_handler, env)
		),
	}, metalanguage.failure_handler, nil)
	--print("val bind", ok, name, _, val)
	if not ok then
		return false, symbol.str
	end
	return true, unit, env:bind_local(terms.binding.let(symbol.str, val))
end

local base_env = {
	["+"] = exprs.host_applicative(function(a, b)
		return a + b
	end, { number, number }, { number }),
	["do"] = exprs.host_operative(do_block, "do_block"),
	val = exprs.host_operative(val_bind, "val_bind"),
}
local env = environment.new_env {
	nonlocals = trie.build(base_env),
}

local ok, res = code:match(
	{ exprs.block(metalanguage.accept_handler, exprs.ExpressionArgs.new(terms.expression_goal.infer, env)) },
	metalanguage.failure_handler,
	nil
)

print(ok, res)

print(res[1])
