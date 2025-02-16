local terms = require "terms"
local evaluator = require "evaluator"
local unanchored_inferrable_term = terms.unanchored_inferrable_term
local anchored_inferrable_term = terms.anchored_inferrable_term
local format = require "format"
local infer = evaluator.infer
local evaluate = evaluator.evaluate
local tc = terms.typechecking_context()
local rc = tc.runtime_context

function test_levels()
	print(unanchored_inferrable_term.level0)
	local suc_term = anchored_inferrable_term(
		format.anchor_here(),
		unanchored_inferrable_term.level_suc(
			anchored_inferrable_term(format.anchor_here(), unanchored_inferrable_term.level0)
		)
	)
	print(suc_term)
	local test_term = anchored_inferrable_term(
		format.anchor_here(),
		unanchored_inferrable_term.level_max(
			suc_term,
			anchored_inferrable_term(format.anchor_here(), unanchored_inferrable_term.level0)
		)
	)
	local ok, inferred_type, usages, typed_term = infer(test_term, tc)
	p(inferred_type)
	assert(inferred_type:is_level_type())
	local result = evaluate(typed_term, rc)
	p(result)
	assert(result:is_level())
	assert(result:unwrap_level() == 1)
	assert(result.level == 1)
end

function test_star()
	local test_term = anchored_inferrable_term(format.anchor_here(), unanchored_inferrable_term.star)
	local ok, inferred_type, inferred_term = infer(test_term, tc)
	p(inferred_type, inferred_term)
	assert(inferred_type.kind == "value_star")
	local result = evaluate(inferred_term, rc)
	p(result)
	assert(result.kind == "value_star")
	assert(result.level == 0)
end
--[[
function test_metavariable_bind_to_other_mv()
	local tcs = terms.typechecker_state()
	local mv_a = tcs:metavariable()
	local mv_b = tcs:metavariable()
	mv_a:bind_metavariable(mv_a) -- noop
	mv_b:bind_metavariable(mv_a) -- mv_b binds to mv_a
	local canonical_a = mv_a:get_canonical()
	local canonical_b = mv_b:get_canonical()
	p(mv_a, mv_b, canonical_a, canonical_b)
	assert(mv_b:get_canonical().id == mv_a.id)
	local mv_c = tcs:metavariable()
	mv_c:bind_metavariable(mv_b)
	assert(mv_c:get_canonical().id == mv_a.id)
	-- check that bound ID was correctly collapsed
	assert(tcs.mvs[mv_c.id].bound_mv_id == mv_a.id)
end
]]

test_levels()
-- FIXME: star isn't implemented as an inferrable term
-- test_star()
--test_metavariable_bind_to_other_mv()
