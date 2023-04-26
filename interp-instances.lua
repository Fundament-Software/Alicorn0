
local ops = require 'basic-operators'
local types = require 'types'

local interpreter = {
  [ops.identity] = function(type_parameters, bound_data, inputs) return inputs end,
  [ops.compose] = function(type_parameters, bound_data, inputs)
    local f, g = inputs[1], inputs[2]
    return function(x) return g(f(x)) end
  end,


  [ops.tuplelift] = function(type_parameters, bound_data, inputs)
    return {inputs}
  end,
  [ops.tupleunlift] = function(type_parameters, bound_data, inputs)
    return inputs[1]
  end,
  [ops.tuplefork] = function(type_parameters, bound_data, inputs)
