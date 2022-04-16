args@{ version ? "linearscan_8_15" }:
(import ./default.nix args).${version}
