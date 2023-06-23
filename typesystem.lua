

-- typeclass : tuple a -> constraint
--

-- indexed sum type
-- parameters may appear in fields that don't
-- indexed product type
-- indexed codata type
--
--

-- A type must be one of
-- - A parameterized kind
-- - A type family invocation
-- - A recursion operator
--
-- A parameterized kind is represented


local hasfixedlayout = {}

local typeerror = {
  kind_mismatch = function(a, b)
    return {
      text = "kind " .. a .. " doesn't match kind " .. b,
      cause = nil
    }
  end,
  param_notidentical = function(idx, cause)
    return {
      text = "parameters weren't identical at position " .. idx,
      cause = cause
    }
  end,
  unification_failed = function(idx, cause)
    return {
      text = "unification required the types at pattern variable " .. idx .. " to match, but they did not",
      cause = cause
    }
  end,
  unrealized_trait = function()
    return {
      text = "the trait required doesn't exist on the specified type"
    }
  end
}

local function typeident(a, b)
  if a.kind ~= b.kind then
    return false, typeerror.kind_mismatch(a.kind, b.kind)
  end
  if #a.params ~= #b.params then
    error "two types were provided different length parameterizations, which is illegal"
  end
  for i = 1, #a.params do
    local ok, err = typeident(a.params[i], b.params[i])
    if not ok then
      return false, typeerror.param_notidentical(i, err)
    end
  end
  return true
end

local function typepat(quantmatch, pattern, subject)
  if subject.kind ~= inputpattern.kind then
    return false, typeerror.kind_mismatch(subject.kind, inputpattern.kind)
  end
  for i, patarg in ipairs(inputpattern.params) do
    if patarg.kind == "variable" then
      if quantmatch[patarg.idx] then
        local ok, err = typeident(quantmatch[patarg.idx], subject.params[i])
        if not ok then
          return false, typeerror.unification_failed(i, err)
        end
      end
    elseif patarg.kind == "pattern" then
      local ok, err = typepat(quantmatch, patarg.pat, subject.params[i])
      if not ok then return false, err end
    end
  end
  return true
end

local function realize_typepat(quantmatch, pattern)
  local res = {kind = pattern.kind, params = {}}
  for i, patarg in ipairs(pattern.params) do
    if patarg.kind == "variable" then
      res[i] = quantmatch[patarg.idx]
    elseif patarg.kind == "pattern" then
      res[i] = realize_typepat(quantmatch, pattern)
    end
  end
  return res
end

local function typematch_args(quantifications, inputpattern, subject, outputpattern)
  local quantmatch = {}
  local ok, err = typepat(quantmatch, inputpattern, subject)
  if not ok, then return false, err end
  return true, realize_typepat(quantmatch, outputpattern)
end

local function realize_trait(trait, subject)
  for _, matcher in ipairs(trait.matchers) do
    local quantmatch = {}
    local ok, err = typepat(quantmatch, inputpattern, subject)
    error "NYI"
  end
end


local number = {kind = "number", params = {}}
local string = {kind = "string", params = {}}
local function primap(arg, res)
  return {kind = "primap", params = {arg, res}}
end

return {
  number = number,
  string = string,
  primap = primap,
  typeident = typeident,
  typepat = typepat,
  realize_typepat = realize_typepat,
  typematch_args = typematch_args
}
