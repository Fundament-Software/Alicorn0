-- SPDX-License-Identifier: Apache-2.0
-- SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

local next, rawget, rawset, type = next, rawget, rawset, type

---@class LuaTrait
---@field declare_method fun(self: LuaTrait, methodname: string)
---@field implement_method_on fun(self: LuaTrait, ty: Type, method_name: string, method: function)
---@field implement_on fun(self: LuaTrait, ty: Type, methods: { [string]: function })
---@field get fun(self: LuaTrait, ty: Type): { [string]: function }

local trait_type_mt = {
	__index = {
		declare_method = function(self, methodname)
			local self_methods = rawget(self, "methods")
			if self_methods[methodname] then
				error("trait " .. self.name .. " method " .. methodname .. " is already declared")
			end
			self_methods[methodname] = true
			rawset(self, "method_count", rawget(self, "method_count") + 1)
		end,
		implement_method_on = function(self, ty, method_name, method)
			local self_impls = rawget(self, "impls")
			if rawget(self_impls, ty) then
				error(("trait %s already implemented on type %s"):format(self.name, tostring(ty)))
			elseif rawget(self, "method_count") ~= 1 then
				error(("trait %s has %d methods, requiring `:implement_on()`"):format(self.name, rawget(self, "method_count")))
			elseif rawget(self, "methods")[method_name] ~= nil and method ~= nil then
				rawset(self_impls, ty, { [method_name] = method })
			else
				error(
					("missing methods to implment trait %s on type %s"):format(self.name, tostring(ty))
				)
			end
		end,
		implement_on = function(self, ty, methods)
			local self_impls, self_methods = rawget(self, "impls"), rawget(self, "methods")
			if rawget(self_impls, ty) then
				error(("trait %s already implemented on type %s"):format(self.name, tostring(ty)))
			end
			local implemented_methods = {}
			local k = next(self_methods)
			while k ~= nil do
				implemented_methods[k] = methods[k]
					or error(("missing method %s implementing trait %s on type %s"):format(k, self.name, tostring(ty)))
				k = next(self_methods, k)
			end
			rawset(self_impls, ty, implemented_methods)
		end,
		get = function(self, ty)
			return rawget(rawget(self, "impls"), ty) or nil --error("trait " .. self.name .. " not implemented on type " .. tostring(ty))
		end,
	},
}

---@param name string
---@return LuaTrait
local function declare_trait(name)
	return setmetatable({ name = name, method_count = 0, methods = {}, impls = {} }, trait_type_mt)
end

-- this trait system is not powerful enough to represent is/unwrap/as
-- but those are exclusive to records and enums, so it's ok
-- eq is not declared as a trait because we'll never use it via traits

local pretty_print = declare_trait("pretty_print")
pretty_print:declare_method("pretty_print")
pretty_print:declare_method("default_print")

local diff = declare_trait("diff")
diff:declare_method("diff")

local value_name = declare_trait("value_name")
value_name:declare_method("value_name")

-- this method not only represents freezing from subsequent mutation, but also
-- returns an existing instance of the argument (if necessary, and structure
-- permitting) to enable efficient hash-consing
local freeze = declare_trait("freeze")
freeze:declare_method("freeze")

-- strict weak order, suitable for table.sort
local order = declare_trait("order")
order:declare_method("compare")

return {
	declare_trait = declare_trait,
	pretty_print = pretty_print,
	diff = diff,
	value_name = value_name,
	freeze = freeze,
	order = order,
}
