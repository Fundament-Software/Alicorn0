local prettyprintable = require "./pretty-printable-trait"
-- record and enum are nominative types.
-- this means that two record types, given the same arguments, are distinct.
-- values constructed from one type are of a different type compared to values
-- constructed from the other.
-- (likewise for enum)

-- foreign, map, and array are structural types.
-- this means that two map types, given the same key-type and value-type, alias
-- each other.
-- values constructed from one type are, at a high level, of the same type
-- as values constructed from the other.
-- (likewise for array, and foreign given the same value_check function;
-- foreign values are constructed elsewhere)

---@class Type
---@field value_check ValueCheckFn
---@field define_enum fun(Type, string, table)
---@field derive fun(Type, Deriver, ...)
---@alias ValueCheckFn fun(val: any): boolean

---@class Value
---@field kind string

-- TODO: are generic annotations powerful enough to describe this function?
-- worked around at the bottom of this file
local function new_self(fn)
	return function(...)
		return fn({}, ...)
	end
end

---@param mt table
---@return ValueCheckFn
local function metatable_equality(mt)
	if type(mt) ~= "table" then
		error("trying to define metatable equality to something that isn't a metatable (possible typo?)")
	end
	return function(val)
		return getmetatable(val) == mt
	end
end

---@alias ParamsWithTypes (string | Type)[]

---@param params_with_types ParamsWithTypes
---@return string[] params
---@return Type[] params_types
local function parse_params_with_types(params_with_types)
	-- params are odd entries of params_with_types
	-- params_types are even
	local params = {}
	local params_types = {}
	local odd = true
	local i = 1
	for _, v in ipairs(params_with_types) do
		if odd then
			params[i] = v
		else
			params_types[i] = v
			i = i + 1
		end
		odd = not odd
	end
	return params, params_types
end

---@param kind string
---@param params string[]
---@param params_types Type[]
---@return nil
local function validate_params_types(kind, params, params_types)
	-- ensure there are at least as many param types as there are params
	-- also ensure there is at least one param
	local at_least_one = false
	for i, v in ipairs(params) do
		at_least_one = true
		local param_type = params_types[i]
		if type(param_type) ~= "table" or type(param_type.value_check) ~= "function" then
			error(
				"trying to set a parameter type to something that isn't a type, in constructor "
					.. kind
					.. ", parameter "
					.. v
					.. " (possible typo?)"
			)
		end
	end
	if not at_least_one then
		error("trying to make a record type, or a record variant of an enum type, with no parameters")
	end
end

-- TODO: cons turns from a table to a callable table. how to conveniently annotate this?
---@param self table
---@param cons table
---@param kind string
---@param params_with_types ParamsWithTypes
---@return table cons
---@return RecordDeriveInfo derive_info
local function gen_record(self, cons, kind, params_with_types)
	local params, params_types = parse_params_with_types(params_with_types)
	validate_params_types(kind, params, params_types)
	setmetatable(cons, {
		__call = function(cons, ...)
			local args = { ... }
			local val = {
				kind = kind,
			}
			for i, v in ipairs(params) do
				local argi = args[i]
				-- type-check constructor arguments
				if params_types[i].value_check(argi) ~= true then
					print("value of parameter " .. v .. ": (follows)")
					p(argi)
					print("expected type of parameter " .. v .. " is :", params_types[i])
					--for i = 2, 25 do
					--	local d = debug.getinfo(i, "Sln")
					--	print(string.format("%s %s %s: %s:%d", d.what, d.namewhat, d.name, d.source, d.currentline))
					--end
					error("wrong argument type passed to constructor " .. kind .. ", parameter '" .. v .. "'")
				end
				val[v] = argi
			end
			setmetatable(val, self)
			return val
		end,
	})
	local derive_info = {
		kind = kind,
		params = params,
		params_types = params_types,
	}
	return cons, derive_info
end

---@class Record: Type
---@field derive fun(self: Record, deriver: Deriver, ...)

---@param self table
---@param kind string
---@param params_with_types ParamsWithTypes
---@return Record self
local function define_record(self, kind, params_with_types)
	local self, derive_info = gen_record(self, self, kind, params_with_types)
	getmetatable(self).__tostring = function()
		return "terms-gen record " .. kind
	end
	function self:derive(deriver, ...)
		return deriver.record(self, derive_info, ...)
	end
	self.value_check = metatable_equality(self)
	self.derive_info = derive_info
	---@cast self Record
	return self
end

---@param self table
---@param kind string
---@return Value val
---@return UnitDeriveInfo derive_info
local function gen_unit(self, kind)
	local val = {
		kind = kind,
	}
	local derive_info = {
		kind = kind,
	}
	setmetatable(val, self)
	return val, derive_info
end

---@class Enum: Type
---@field derive fun(self: Enum, deriver: Deriver, ...)

---@alias Variants [ string, ParamsWithTypes ][]

---@param self table
---@param name string
---@param variants Variants
---@return Enum self
local function define_enum(self, name, variants)
	setmetatable(self, nil)
	local derive_variants = {}
	for i, v in ipairs(variants) do
		local vname = v[1]
		local vparams_with_types = v[2]
		local kind = name .. "." .. vname
		derive_variants[i] = vname
		if vparams_with_types then
			local record_cons, record_info = gen_record(self, {}, kind, vparams_with_types)
			self[vname] = record_cons
			derive_variants[vname] = {
				type = "record",
				info = record_info,
			}
		else
			local unit_val, unit_info = gen_unit(self, kind)
			self[vname] = unit_val
			derive_variants[vname] = {
				type = "unit",
				info = unit_info,
			}
		end
	end
	setmetatable(self, {
		__tostring = function()
			return "terms-gen enum " .. name
		end,
	})
	local derive_info = {
		name = name,
		variants = derive_variants,
	}
	function self:derive(deriver, ...)
		return deriver.enum(self, derive_info, ...)
	end
	self.value_check = metatable_equality(self)
	self.derive_info = derive_info
	---@cast self Enum
	return self
end

---@class Foreign: Type

---@param self table
---@param value_check ValueCheckFn
---@param lsp_type string?
---@return Foreign self
local function define_foreign(self, value_check, lsp_type)
	setmetatable(self, {
		__tostring = function()
			return "terms-gen foreign " .. (lsp_type or "unknown")
		end,
	})
	self.value_check = value_check
	self.derive_info = {
		kind = "foreign",
		lsp_type = lsp_type,
	}
	---@cast self Foreign
	return self
end

local map_type_mt = {
	__call = function(self)
		local val = {
			_map = {},
		}
		setmetatable(val, self)
		return val
	end,
	__eq = function(left, right)
		return left.key_type == right.key_type and left.value_type == right.value_type
	end,
}

---@class Map: Type

local function map_prettyprintable(self, printer, ...)
	return printer:table(self._map, ...)
end

local map_methods = {
	pairs = function(self)
		return pairs(self._map)
	end,
	-- TODO: default_print?
	pretty_print = function(self, ...)
		local pp = require("./pretty-printer").PrettyPrint.new()
		map_prettyprintable(self, pp, ...)
		return tostring(pp)
	end,
	get = function(self, key)
		local mt = getmetatable(self)
		local key_type = mt.key_type
		local value_type = mt.value_type
		if key_type.value_check(key) ~= true then
			p("map-get", key_type, value_type)
			p(key)
			error("wrong key type passed to map:get")
		end
		return self._map[key]
	end,
	set = function(self, key, value)
		local mt = getmetatable(self)
		local key_type = mt.key_type
		local value_type = mt.value_type
		if key_type.value_check(key) ~= true then
			p("map-set", key_type, value_type)
			p(key)
			error("wrong key type passed to map:set")
		end
		if value_type.value_check(value) ~= true then
			p("map-set", key_type, value_type)
			p(value)
			error("wrong value type passed to map:set")
		end
		self._map[key] = value
	end,
}

local function gen_map_fns(key_type, value_type)
	local function index(self, key)
		local method = map_methods[key]
		if method then
			return method
		end
		error("indexing of maps is disallowed. use :get()")
	end
	local function newindex(self, key, value)
		error("index-assignment of maps is disallowed. use :set()")
	end
	return index, newindex
end

-- TODO: memoize? otherwise LOTS of tables will be constructed,
-- through repeated calls to declare_map
---@param self table
---@param key_type Type
---@param value_type Type
---@return Map self
local function define_map(self, key_type, value_type)
	if
		type(key_type) ~= "table"
		or type(key_type.value_check) ~= "function"
		or type(value_type) ~= "table"
		or type(value_type.value_check) ~= "function"
	then
		error("trying to set the key or value type to something that isn't a type (possible typo?)")
	end
	setmetatable(self, map_type_mt)
	self.key_type = key_type
	self.value_type = value_type
	self.__index, self.__newindex = gen_map_fns(key_type, value_type)
	self.__pairs = map_methods.pairs
	prettyprintable:implement_on(self, {
		print = map_prettyprintable,
	})
	-- NOTE: this isn't primitive equality; this type has a __eq metamethod!
	self.value_check = metatable_equality(self)
	---@cast self Map
	return self
end

local set_type_mt = {
	__call = function(self)
		local val = {
			_set = {},
		}
		setmetatable(val, self)
		return val
	end,
	__eq = function(left, right)
		return left.key_type == right.key_type
	end,
}

---@class Set: Type

local function set_prettyprintable(self, printer, ...)
	return printer:table(self._set, ...)
end

local set_methods = {
	put = function(self, key)
		local mt = getmetatable(self)
		local key_type = mt.key_type
		if key_type.value_check(key) ~= true then
			p("set-put", key_type)
			p(key)
			error("wrong key type passed to set:put")
		end
		self._set[key] = true
	end,
	reset = function(self, key)
		local mt = getmetatable(self)
		local key_type = mt.key_type
		if key_type.value_check(key) ~= true then
			p("set-reset", key_type)
			p(key)
			error("wrong key type passed to set:reset")
		end
		self._set[key] = nil
	end,
	test = function(self, key)
		local mt = getmetatable(self)
		local key_type = mt.key_type
		if key_type.value_check(key) ~= true then
			p("set-test", key_type)
			p(key)
			error("wrong key type passed to set:test")
		end
		return self._set[key]
	end,
	-- just ignore the second value of the iterations :)
	pairs = function(self)
		return pairs(self._set)
	end,
	-- TODO: default_print?
	pretty_print = function(self, ...)
		local pp = require("./pretty-printer").PrettyPrint.new()
		set_prettyprintable(self, pp, ...)
		return tostring(pp)
	end,
	copy = function(self, onto)
		if not onto then
			local mt = getmetatable(self)
			onto = mt()
		end
		for k in self:pairs() do
			onto:set(k)
		end
		return onto
	end,
	union = function(self, other)
		local st = getmetatable(self)
		local ot = getmetatable(other)
		if st ~= ot then
			error("set:union must be passed sets of the same type")
		end
		local new = self:copy()
		other:copy(new)
		return new
	end,
	subtract = function(self, other)
		local st = getmetatable(self)
		local ot = getmetatable(other)
		if st ~= ot then
			error("set:subtract must be passed sets of the same type")
		end
		local new = self:copy()
		for k in other:pairs() do
			new:reset(k)
		end
		return new
	end,
}

---@param self table
---@param key_type Type
---@return Set self
local function define_set(self, key_type)
	if type(key_type) ~= "table" or type(key_type.value_check) ~= "function" then
		error("trying to set the key or value type to something that isn't a type (possible typo?)")
	end
	setmetatable(self, set_type_mt)
	self.key_type = key_type
	self.__index = set_methods
	prettyprintable:implement_on(self, {
		print = set_prettyprintable,
	})
	-- NOTE: this isn't primitive equality; this type has a __eq metamethod!
	self.value_check = metatable_equality(self)
	return self
end

local array_type_mt = {
	__call = function(self, ...)
		local val = {
			n = 0,
			array = {},
		}
		setmetatable(val, self)
		local args = { ... }
		for i = 1, select("#", ...) do
			val:append(args[i])
		end
		return val
	end,
	__eq = function(left, right)
		return left.value_type == right.value_type
	end,
}

---@class Array: Type

local function array_prettyprintable(self, printer, ...)
	return printer:array(self.array, ...)
end

local array_methods = {
	ipairs = function(self)
		return ipairs(self.array)
	end,
	len = function(self)
		return self.n
	end,
	append = function(self, val)
		self[self.n + 1] = val
	end,
	eq = function(self, other)
		if self:len() ~= other:len() then
			return false
		end
		for i = 1, self:len() do
			if self[i] ~= other[i] then
				return false
			end
		end
		return true
	end,
	copy = function(self, first, last)
		local first = first or 1
		local last = last or self:len()
		local mt = getmetatable(self)
		local new = mt()
		for i = first, last do
			new:append(self.array[i])
		end
		return new
	end,
	unpack = function(self)
		return table.unpack(self.array)
	end,
	-- TODO: default_print?
	pretty_print = function(self, ...)
		local pp = require("./pretty-printer").PrettyPrint.new()
		array_prettyprintable(self, pp, ...)
		return tostring(pp)
	end,
	diff = function(self, other)
		print("diffing array...")
		local st = getmetatable(self)
		local ot = getmetatable(other)
		print("value_type: " .. tostring(st.value_type))
		if st ~= ot then
			print("unequal types!")
			print(st)
			print(ot)
			print("stopping diff")
			return
		end
		if self:len() ~= other:len() then
			print("unequal lengths!")
			print(self:len())
			print(other:len())
			print("stopping diff")
			return
		end
		local n = 0
		local diff_elems = {}
		for i = 1, self:len() do
			if self[i] ~= other[i] then
				n = n + 1
				diff_elems[n] = i
			end
		end
		if n == 0 then
			print("no difference")
			print("stopping diff")
			return
		elseif n == 1 then
			local d = diff_elems[1]
			print("difference in element: " .. tostring(d))
			if self[d].diff then
				-- tail call
				return self[d]:diff(other[d])
			else
				print("stopping diff (missing diff method)")
				return
			end
		else
			print("difference in multiple elements:")
			for i = 1, n do
				print(diff_elems[i])
			end
			print("stopping diff")
			return
		end
	end,
}

local function gen_array_fns(value_type)
	local function index(self, key)
		local method = array_methods[key]
		if method then
			return method
		end
		if type(key) ~= "number" then
			p("array-index", value_type)
			p(key)
			error("wrong key type passed to array indexing")
		end
		-- check if integer
		-- there are many nice ways to do this in lua >=5.3
		-- unfortunately, this is not us
		if math.floor(key) ~= key then
			p(key)
			error("key passed to array indexing is not an integer")
		end
		if key < 1 or key > self.n then
			p(key, self.n)
			error("key passed to array indexing is out of bounds")
		end
		return self.array[key]
	end
	local function newindex(self, key, value)
		if type(key) ~= "number" then
			p("array-index", value_type)
			p(key)
			error("wrong key type passed to array index-assignment")
		end
		if math.floor(key) ~= key then
			p(key)
			error("key passed to array index-assignment is not an integer")
		end
		-- n+1 can be used to append
		if key < 1 or key > self.n + 1 then
			p(key, self.n)
			error("key passed to array index-assignment is out of bounds")
		end
		if value_type.value_check(value) ~= true then
			p("array-index-assign", value_type)
			p(value)
			error("wrong value type passed to array index-assignment")
		end
		self.array[key] = value
		if key > self.n then
			self.n = key
		end
	end
	return index, newindex
end

-- TODO: see define_map
---@param self table
---@param value_type Type
---@return Array self
local function define_array(self, value_type)
	if type(value_type) ~= "table" or type(value_type.value_check) ~= "function" then
		error("trying to set the value type to something that isn't a type (possible typo?)")
	end
	setmetatable(self, array_type_mt)
	self.value_type = value_type
	self.__index, self.__newindex = gen_array_fns(value_type)
	self.__ipairs = array_methods.ipairs
	self.__len = array_methods.len
	self.__tostring = self:__index("pretty_print")
	self.__eq = array_methods.eq
	prettyprintable:implement_on(self, {
		print = array_prettyprintable,
	})
	-- NOTE: this isn't primitive equality; this type has a __eq metamethod!
	self.value_check = metatable_equality(self)
	---@cast self Array
	return self
end

local type_mt = {
	__index = {
		define_record = define_record,
		define_enum = define_enum,
		define_foreign = define_foreign,
		define_map = define_map,
		define_array = define_array,
	},
}

---@type ValueCheckFn
local function undefined_value_check(val)
	error("trying to typecheck a value against a type that has been declared but not defined")
end

---@class UndefinedType: Type
---@field define_record fun(self: table, kind: string, params_with_types: ParamsWithTypes): Record
---@field define_enum fun(self: table, name: string, variants: Variants): Enum
---@field define_foreign fun(self: table, value_check: ValueCheckFn): Foreign
---@field define_map fun(self: table, key_type: Type, value_type: Type): Map
---@field define_array fun(self: table, value_type: Type): Array

---@param self table
---@return UndefinedType self
local function define_type(self)
	setmetatable(self, type_mt)
	self.value_check = undefined_value_check
	---@cast self UndefinedType
	return self
end

---@param typename string
---@return Foreign
local function gen_builtin(typename)
	return define_foreign({}, function(val)
		return type(val) == typename
	end, typename)
end

local terms_gen = {
	---@type fun(kind: string, params_with_types: ParamsWithTypes): Record
	declare_record = new_self(define_record),
	---@type fun(name: string, variants: Variants): Enum
	declare_enum = new_self(define_enum),
	-- Make sure the function you pass to this returns true, not just a truthy value
	---@type fun(value_check: ValueCheckFn): Foreign
	declare_foreign = new_self(define_foreign),
	---@type fun(key_type: Type, value_type: Type): Map
	declare_map = new_self(define_map),
	---@type fun(key_type: Type): Set
	declare_set = new_self(define_set),
	---@type fun(value_type: Type): Array
	declare_array = new_self(define_array),
	---@type fun(): UndefinedType
	declare_type = new_self(define_type),
	metatable_equality = metatable_equality,
	builtin_number = gen_builtin("number"),
	builtin_string = gen_builtin("string"),
	builtin_function = gen_builtin("function"),
	anchor_type = define_foreign({}, function(o)
		if o and o.sourceid then
			return true
		end
		return false
	end),
	any_lua_type = define_foreign({}, function()
		return true
	end),
}
local internals_interface = require "./internals-interface"
internals_interface.terms_gen = terms_gen
return terms_gen
