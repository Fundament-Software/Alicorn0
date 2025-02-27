// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

use mlua::prelude::*;

const ALICORN: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/alicorn.lua"));
const PRELUDE: &[u8] = include_bytes!("prelude.alc");
const GLSL_PRELUDE: &[u8] = include_bytes!("glsl-prelude.alc");

extern "C-unwind" {
    fn luaopen_lpeg(L: *mut mlua::lua_State) -> std::ffi::c_int;
    fn luaopen_lfs(L: *mut mlua::lua_State) -> std::ffi::c_int;
}

pub struct Alicorn {
    lua: Lua,
}

impl Alicorn {
    pub fn new(lua: Option<Lua>) -> Result<Self, mlua::Error> {
        let lua = lua.unwrap_or_else(|| Lua::new());

        // Load C libraries we already linked into our rust binary using our build script. This works because we can
        // declare the C functions directly and have the linker resolve them during the link step.
        unsafe {
            let _: mlua::Value =
                lua.load_from_function("lpeg", lua.create_c_function(luaopen_lpeg)?)?;
            let _: mlua::Value =
                lua.load_from_function("lfs", lua.create_c_function(luaopen_lfs)?)?;
        }

        lua.load(
            r#"
jit.opt.start("maxtrace=10000")
jit.opt.start("maxmcode=4096")
jit.opt.start("recunroll=5")
jit.opt.start("loopunroll=60")
        "#,
        )
        .exec()?;

        // Here, we load all the embedded alicorn source into the lua engine and execute it.
        lua.load(ALICORN).exec()?;

        // Then we create helper functions for compiling an alicorn source file that we can bind to mlua.
        lua.load(
            r#" 
metalanguage = require "metalanguage"
evaluator = require "evaluator"
format = require "format-adapter"
formatter = require "format"
base_env = require "base-env"
terms = require "terms"
exprs = require "alicorn-expressions"
profile = require "profile"
util = require "alicorn-utils"

env = base_env.create()
original_env, env = env:enter_block(terms.block_purity.effectful)

function alc_process(code, cur_env)
	local ok, expr, inner_env = code:match({
		exprs.top_level_block(
			metalanguage.accept_handler,
			{ exprargs = exprs.ExpressionArgs.new(terms.expression_goal.infer, cur_env), name = name }
		),
	}, metalanguage.failure_handler, nil)

  if not ok then
    print(tostring(expr))
    error("processing failed (error printed to stdout)")
  end
  
  return expr, inner_env
end

function alc_include_string(src, name)
  local bound_expr, inner_env = alc_process(format.read(src, name), env)
  env = inner_env
  return bound_expr
end

function alc_include_file(filename)
  local f = io.open(filename)
  if not f then
    error("Couldn't find " .. filename)
  end

  local s = format.read(f:read("a"), filename)
  f:close()
  local bound_expr, inner_env = alc_process(s, env)
  env = inner_env
  return bound_expr
end

function alc_evaluate(bound_expr, cur_env)
	local ok, type, usages, term = evaluator.infer(bound_expr, cur_env.typechecking_context)

  if not ok then
    print(tostring(type))
    error("inference failed (error printed to stdout)")
	end
  
  local gen = require "terms-generators"
  local set = gen.declare_set
  local unique_id = gen.builtin_table
  
  local ok, err = evaluator.typechecker_state:flow(
    type,
    cur_env.typechecking_context,
    terms.flex_value.program_type(
      terms.flex_value.effect_row(terms.unique_id_set(terms.TCState, terms.lua_prog)),
      evaluator.typechecker_state:metavariable(cur_env.typechecking_context):as_flex()
    ),
    cur_env.typechecking_context,
    terms.constraintcause.primitive("final flow check", formatter.anchor_here())
  )
    
  if not ok then
    print(err)
    error("flow check failed (error printed to stdout)")
  end

  return pcall(function()
		return evaluator.evaluate(term, cur_env.typechecking_context.runtime_context, cur_env.typechecking_context)
	end)
end

function alc_execute(src, name)
	local shadowed, cur_env = env:enter_block(terms.block_purity.effectful)

  local bound_expr, cur_env = alc_process(format.read(src, name), cur_env)

  local cur_env, block_expr, _ = cur_env:exit_block(bound_expr, shadowed)

  local ok, result = alc_evaluate(block_expr, cur_env)

  if not ok then
    print(result)
    error("evaluation failed (error printed to stdout)")
  end

  local result_exec = evaluator.execute_program(result)
  return result_exec:unwrap_host_tuple_value():unpack()
end

function alc_execute_file(filename)
  local f = io.open(filename)
  if not f then
    error("Couldn't find " .. filename)
  end

  local s = format.read(f:read("a"), filename)
  f:close()
  return alc_execute(s, filename)
end
        "#,
        )
        .exec()?;

        let alicorn = Self { lua };

        let _ = alicorn.include(std::str::from_utf8(PRELUDE)?, "prelude.alc")?;

        Ok(alicorn)
    }

    pub fn load_glsl_prelude(&self) -> Result<(), mlua::Error> {
        let _ = self.include(std::str::from_utf8(GLSL_PRELUDE)?, "glsl-prelude.alc")?;

        Ok(())
    }

    pub fn include(
        &self,
        source: impl AsRef<str>,
        name: impl AsRef<str>,
    ) -> Result<mlua::Value, mlua::Error> {
        let alc_include_string: LuaFunction = self.lua.load("alc_include_string").eval()?;

        alc_include_string.call((source.as_ref(), name.as_ref()))
    }
    pub fn include_file(
        &self,
        path: impl AsRef<std::path::Path>,
    ) -> Result<mlua::Value, mlua::Error> {
        let alc_include_file: LuaFunction = self.lua.load("alc_include_file").eval()?;

        alc_include_file.call(path.as_ref().as_os_str().to_string_lossy())
    }

    pub fn execute<R: FromLuaMulti>(
        &self,
        source: impl AsRef<str>,
        name: impl AsRef<str>,
    ) -> Result<R, mlua::Error> {
        let execute_program: LuaFunction = self.lua.load("alc_execute").eval()?;
        execute_program.call((source.as_ref(), name.as_ref()))
    }

    pub fn execute_file<R: FromLuaMulti>(
        &self,
        path: impl AsRef<std::path::Path>,
    ) -> Result<R, mlua::Error> {
        let execute_program: LuaFunction = self.lua.load("alc_execute_path").eval()?;
        execute_program.call(path.as_ref().as_os_str().to_string_lossy())
    }
}

#[test]
fn test_runtest_file() {
    // set the working directory to some random temporary folder to sabotage loading any of the files from this crate, as a crate including this one wouldn't have access to those files
    let old = std::env::current_dir().unwrap();
    let temp_dir = std::env::temp_dir();
    let root = std::path::Path::new(&temp_dir);
    std::env::set_current_dir(&root).unwrap();

    let alicorn = Alicorn::new(None).unwrap();

    // Restore working dir so we can find prelude.alc
    std::env::set_current_dir(&old).unwrap();
    let result: LuaValue = alicorn
        .execute(
            "host-tuple-of(tuple-desc-singleton(host-type, host-number))(4)",
            format!("{}:{}", file!(), line!() - 1),
        )
        .unwrap();
    assert_eq!(result, LuaValue::Integer(4));
}
