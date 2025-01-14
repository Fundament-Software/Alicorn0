local metalanguage = require "metalanguage"
local alicorn = require "alicorn-evaluator"
local conexpr = require "contextual-exprs"
local environment = require "environment"
local format = require "format"

local val = metalanguage.primitive_operative(function(syntax, env)
	local ok, name, expr, nextenv = syntax:match({
		metalanguage.listmatch(
			metalanguage.accept_handler,
			metalanguage.any(
				metalanguage.listof(metalanguage.accept_handler, metalanguage.issymbol(metalanguage.accept_handler)),
				metalanguage.issymbol(metalanguage.accept_handler)
			),
			metalanguage.symbol_exact(metalanguage.accept_handler, "="),
			alicorn.evaluates(metalanguage.accept_handler, env)
		),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return false, name
	end
	local binder, envres
	if type(name) == "string" then
		binder = conexpr.bindval(name)
	elseif not (name["kind"] or format.is_symbol(name)) then
		binder = conexpr.bindtuple(name)
	else
		error "names had an invalid value?"
	end
end)
