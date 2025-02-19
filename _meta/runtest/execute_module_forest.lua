-- SPDX-License-Identifier: Apache-2.0
-- SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

---@meta

---@param module_forest string[]
---@param env Environment
---@param log function
---@param on_success fun(module_tree: runtest._module_tree, expr_failure_point: failure_point, expr: (anchored_inferrable | nil), expr_env: Environment): (control: runtest.execution_control)
---@param on_failure fun(module_tree: runtest._module_tree, expr_failure_point: failure_point, expr: (anchored_inferrable | nil), expr_env: Environment): (control: runtest.failure_execution_control)
---@return runtest.execution_control control
local function execute_module_forest(module_forest, env, log, on_success, on_failure) end

return execute_module_forest
