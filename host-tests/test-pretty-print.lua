local PrettyPrint = require "pretty-printer".PrettyPrint
local luaunit = require "luaunit"
local terms_gen = require "terms-generators"
local terms = require "terms"
local U = require "alicorn-utils"

local value_array = terms_gen.declare_array(terms.value)
-- if this require fails you need to `lit install luvit/tap`
local passed, failed, total = (require "tap")(function(test)
	-- test cases are assuming that fitsinto(not a type, _) or fitinto(_, not a type)
	-- returns false, errormessage
	-- but it would probably be fine for passing things that aren't types into fitsinto
	-- to throw a lua error() instead
	-- important part is that it doesn't return true!

	test("empty pretty printer result is empty", function(expect)
		local pp = PrettyPrint.new()
		assert(tostring(pp) == "")
	end)

	test("array", function(expect)
		local pp = PrettyPrint.new()
		pp:any(value_array(terms.value.host_number_type, terms.value.host_number_type))
		local out = U.strip_ansi(tostring(pp))
		luaunit.assertEquals(out, "[value.host_number_type, value.host_number_type]")
	end)

	test("simple unit type", function(expect)
		local pp = PrettyPrint.new()
		pp:unit("values.level_type")
		local out = U.strip_ansi(tostring(pp))
		assert(out == "values.level_type")
	end)

	test("simple record type", function(expect)
		local pp = PrettyPrint.new()
		pp:record("values.any", { { "value", "something" } })
		local out = U.strip_ansi(tostring(pp))
		luaunit.assertEquals(out, [[values.any("something")]])
	end)

	test("complex record type", function(expect)
		local pp = PrettyPrint.new()
		pp:record("values.table", {
			{ "int", 1 },
			{ "value", "something" },
		})
		local out = U.strip_ansi(tostring(pp))
		luaunit.assertEquals(
			out,
			[[values.table {
 int = 1,
 value = "something",
}]]
		)
	end)
end)
