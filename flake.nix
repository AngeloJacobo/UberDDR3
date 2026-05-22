{
  description = "UberDDR3 OpenXC7 development shell";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    toolchain-nix.url = "github:openXC7/toolchain-nix";
    nixpkgs.follows = "toolchain-nix/nixpkgs";
  };

  outputs = { flake-utils, nixpkgs, toolchain-nix, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        openXc7Shell = toolchain-nix.devShell.${system};
        nextpnrXilinx = toolchain-nix.packages.${system}.nextpnr-xilinx;
        originalPrjxrayDb = "${nextpnrXilinx}/share/nextpnr/external/prjxray-db";
        patchedPrjxrayDb = pkgs.runCommand "prjxray-db-kintex7-lioi3-tbytesrc-oclkm-overlay" { } ''
          mkdir -p $out
          cp -a ${originalPrjxrayDb}/kintex7 $out/kintex7

          for db_file in \
            $out/kintex7/segbits_lioi3_tbytesrc.db \
            $out/kintex7/segbits_lioi3_tbytesrc.origin_info.db
          do
            chmod u+w "$db_file"
          done

          if ! grep -q "^LIOI3_TBYTESRC.IOI_OCLKM_0.IOI_IMUX31_1 " \
            $out/kintex7/segbits_lioi3_tbytesrc.db
          then
            cat >> $out/kintex7/segbits_lioi3_tbytesrc.db <<EOF
LIOI3_TBYTESRC.IOI_OCLKM_0.IOI_IMUX31_1 30_94 31_83 31_93
EOF
          fi

          if ! grep -q "^LIOI3_TBYTESRC.IOI_OCLKM_0.IOI_IMUX31_1 " \
            $out/kintex7/segbits_lioi3_tbytesrc.origin_info.db
          then
            cat >> $out/kintex7/segbits_lioi3_tbytesrc.origin_info.db <<EOF
LIOI3_TBYTESRC.IOI_OCLKM_0.IOI_IMUX31_1 origin:037-iob-pips 30_94 31_83 31_93
EOF
          fi
        '';
      in {
        devShells.default = pkgs.mkShell {
          inputsFrom = [ openXc7Shell ];
          shellHook = ''
            ${openXc7Shell.shellHook or ""}
            export PRJXRAY_DB_DIR="${patchedPrjxrayDb}"
          '';
        };
      });
}
