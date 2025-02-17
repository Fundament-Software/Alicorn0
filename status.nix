{ system ? builtins.currentSystem }:
let flake = builtins.getFlake (toString ./.);
in flake.checks.${system} // { recurseForDerivations = true; }
