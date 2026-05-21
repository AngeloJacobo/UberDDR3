{
  description = "UberDDR3 OpenXC7 development shell";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    toolchain-nix.url = "github:openXC7/toolchain-nix";
  };

  outputs = { flake-utils, toolchain-nix, ... }:
    flake-utils.lib.eachDefaultSystem (system: {
      devShells.default = toolchain-nix.devShell.${system};
    });
}
