
local lang = require "./metalanguage"

-- for k, v in pairs(lang) do print(k, v) end

local symbol, value, list = lang.symbol, lang.value, lang.list

local code =
  list(
    symbol "+",
    value(1),
    value(2)
  )

local env =
  lang.newenv {
    ["+"] = lang.primitive_applicative(function(a, b) return a + b end)
  }

local ok, res = lang.eval(code, env)

print(ok, res)

print(res[1])
