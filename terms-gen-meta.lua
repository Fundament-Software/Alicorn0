local terms = require "./terms"
local acg = require "abstract-codegen"
local io = require "io"

-- minimal example:
-- ---@meta "purity"

-- ---@class (exact) purity
-- purity = {}

-- ---@return boolean
-- function purity:is_pure() end
-- ---@return boolean
-- function purity:is_effectful() end

-- ---@class (exact) PurityType:Type
-- ---@field pure purity
-- ---@field effectful purity
-- return {}

local meta_gen = acg.generator {
	file = [[-- THIS FILE AUTOGENERATED BY terms-gen-meta.lua
---@meta "$filename"
$definition
]],
	is_method = [[---@return boolean
function $typename:is_$variant() end]],
	unwrap_method = [[---@return $(, )parts
function $typename:unwrap_$variant() end]],
	as_method = [[---@return boolean, $(, )parts
function $typename:as_$variant() end]],
	enum_definition = [[---@class (exact) $typename
---@field kind string
---@field pretty_print fun(...)
$typename = {}
$(
)methods
---@class (exact) $moduletypename:Type
$(
)constructors
return {}]],
	unit_constructor = [[---@field $variant $typename]],
	record_constructor = [[---@field $variant fun($(, )params): $typename]],
}

local function build_meta_file_for_enum(info)
	local kind = info.name
	local methods = {}
	local constructors = {}
	-- p(info)
	for _, variant in ipairs(info.variants) do
		local vinfo = info.variants[variant]
		--p(vinfo)
		if vinfo.type == "record" then
			local params = {}
			local paramtypes = {}
			for i, param in ipairs(vinfo.info.params_types) do
				local pname = vinfo.info.params[i]
				local ptype
				if not param or not param.derive_info then
					ptype = "any"
				else
					if param.derive_info.kind == "foreign" then
						ptype = param.derive_info.lsp_type or "any"
					else
						ptype = param.derive_info.name or "any"
					end
				end
				params[#params + 1] = pname .. ":" .. ptype
				paramtypes[#paramtypes + 1] = ptype
			end
			constructors[#constructors + 1] = {
				kind = "record_constructor",
				typename = kind,
				variant = variant,
				params = params,
			}
			methods[#methods + 1] = {
				kind = "is_method",
				typename = kind,
				variant = variant,
			}
			methods[#methods + 1] = {
				kind = "unwrap_method",
				typename = kind,
				variant = variant,
				parts = paramtypes,
			}
			methods[#methods + 1] = {
				kind = "as_method",
				typename = kind,
				variant = variant,
				parts = paramtypes,
			}
		elseif vinfo.type == "unit" then
			constructors[#constructors + 1] = {
				kind = "unit_constructor",
				typename = kind,
				variant = variant,
			}
			methods[#methods + 1] = {
				kind = "is_method",
				typename = kind,
				variant = variant,
			}
		else
			p(vinfo)
			error "unknown variant type"
		end
	end
	return meta_gen {
		kind = "file",
		filename = kind .. ".lua",
		definition = {
			kind = "enum_definition",
			typename = kind,
			moduletypename = kind .. "Type",
			methods = methods,
			constructors = constructors,
		},
	}
end

---@type Deriver
local gen_type = {
	record = function(t, info)
		-- p(info)
	end,
	enum = function(t, info)
		local file = io.open("types/" .. info.name .. ".lua", "wb")
		if file then
			file:write(build_meta_file_for_enum(info))
			file:close()
		end
	end,
}

for k, v in pairs(terms) do
	if k and type(v) == "table" and v.derive then
		v:derive(gen_type)
		-- print(k)
		-- for a, b in pairs(v.meta) do
		--     print("", a, b)
		-- end
		-- for a, b in pairs(getmetatable(v)) do
		--     print(a, b)
		-- end
	end
end

return {}
