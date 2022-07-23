args@{ version ? "coq-linearscan_8_15", pkgs ? null }:
(import ./default.nix args).${version}
