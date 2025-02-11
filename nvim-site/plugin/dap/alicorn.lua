local api = vim.api
if not api.nvim_create_user_command then
	return
end

api.nvim_create_user_command("DapLoadAlicornConfig", function(opts)
	local dap = require("dap")
	if opts.bang or dap.adapters.luaMobDebug == nil then
		function dap.adapters.luaMobDebug(on_config, dap_configuration, parent_session)
			local port = dap_configuration.listenPort
			if port == nil then
				port = "${port}"
			end
			local executable = nil
			if dap_configuration.request == "launch" then
				local args = dap_configuration.args
				if port ~= "${port}" then
					if args then
						for idx, arg in pairs(args) do
							args[idx] = arg:gsub("${port}", tostring(port))
						end
					end
				end
				executable = {
					command = dap_configuration.interpreter,
					args = args,
					cwd = dap_configuration.workingDirectory,
					detached = false,
				}
			elseif dap_configuration.request == "attach" then
			else
				require("dap.utils").notify(string.format("unknown request %q; aborted", dap_configuration.request))
				return
			end
			on_config({
				type = "server",
				host = dap_configuration.listenPublicly and "0.0.0.0" or "127.0.0.1",
				port = port,
				executable = executable,
			})
		end
	end
	require("dap.ext.vscode").load_launchjs(nil, {
		luaMobDebug = { "lua" },
	})
end, {
	bang = true,
	bar = true,
	nargs = 0,
})
