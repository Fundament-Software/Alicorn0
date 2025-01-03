local derivers = require "derivers"
local eq = derivers.eq
local gen = require "terms-generators"

local mytype1 = gen.declare_enum("mytype1", {
	{ "foo" },
	{ "bar" },
	{ "baz" },
})

local mytype2 = gen.declare_enum("mytype2", {
	{ "truer" },
	{ "middle", { "thing", mytype1 } },
	{ "falser" },
})

local mytype3 = gen.declare_record("mytype3", {
	"one",
	mytype1,
	"anotherone",
	mytype2,
})

local mytype3butsimple = gen.declare_record("mytype3", {
	"one",
	gen.builtin_number,
	"anotherone",
	gen.builtin_number,
})

--print("simple")
mytype3butsimple:derive(eq)
--mytype3butsimple:derive(derivers.pretty_print)
local x = mytype3butsimple(69, 420)
local y = mytype3butsimple(420, 69)
local z = mytype3butsimple(69, 420)
assert(x ~= y)
assert(x == z)
assert(y ~= z)
--print(x:pretty_print())

--print("2")
-- beware of bugs if mytype2 doesn't derive eq
-- mytype1 is an enum with only unit cases, so equality is trivial
mytype2:derive(eq)
mytype3:derive(eq)
local x2 = mytype3(mytype1.foo, mytype2.truer)
local y2 = mytype3(mytype1.bar, mytype2.truer)
local y3 = mytype3(mytype1.bar, mytype2.truer)
local z2 = mytype3(mytype1.foo, mytype2.falser)
local a2 = mytype3(mytype1.foo, mytype2.middle(mytype1.bar))
local b2 = mytype3(mytype1.foo, mytype2.middle(mytype1.baz))
local c2 = mytype3(mytype1.foo, mytype2.middle(mytype1.baz))
assert(x2 ~= y2)
assert(x2 ~= z2)
assert(x2 ~= a2)
assert(x2 ~= b2)
assert(y2 ~= z2)
assert(y2 ~= a2)
assert(y2 ~= b2)
assert(z2 ~= a2)
assert(z2 ~= b2)
assert(a2 ~= b2)
assert(b2 == c2)
assert(y2 == y3)

print("Success!")
