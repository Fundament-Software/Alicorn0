local gen = require "../terms-generators"
local map = gen.declare_map
local array = gen.declare_array

local typed = gen.declare_type()
typed:define_enum("typed", {
	{ "recordcons", { "fields", map(gen.builtin_string, typed) } },
	{ "tuplecons", { "methods", array(typed) } },
})

local map_string_typed = map(gen.builtin_string, typed)
local stuff = map_string_typed()
local funvalue = typed.recordcons(stuff)
--p(funvalue)

local stuff2 = map_string_typed()
stuff2:set("foo", funvalue)
local funvalue2 = typed.recordcons(stuff2)
--p(funvalue2)

for k, v in pairs(funvalue2.fields) do
	--p(k, v)
	assert(k == "foo")
	assert(v == funvalue)
end

local function runfail(f)
	print("start debug")
	local success, err = pcall(f)
	print("end debug")
	assert(not success)
	--p(err)
end

runfail(function()
	stuff2:set(2, funvalue)
end)
runfail(function()
	stuff2:set("bar", "baz")
end)
runfail(function()
	stuff2:set("foo", "quux")
end)

local array_typed = array(typed)
local athing = array_typed()
athing:append(funvalue)
athing[2] = funvalue2
local funvalue3 = typed.tuplecons(athing)
--p(funvalue3)
assert(#funvalue3.methods == 2)

for i, v in ipairs(funvalue3.methods) do
	--p(i, v)
	if i == 1 then
		assert(v == funvalue)
	elseif i == 2 then
		assert(v == funvalue2)
	else
		error("bad")
	end
end

local athing2 = array_typed(funvalue, funvalue2)
--p(athing2)
assert(#athing2 == 2)
athing2[1] = funvalue2
--p(athing2)
assert(#athing2 == 2)

runfail(function()
	athing["lol"] = funvalue
end)
runfail(function()
	athing[2] = "ping"
end)
runfail(function()
	athing[0] = "pong"
end)
runfail(function()
	athing[69] = "nice"
end)

print("Success!")
