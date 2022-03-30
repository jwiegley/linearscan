args@{
  rev    ? "9222ae36b208d1c6b55d88e10aa68f969b5b5244"
, sha256 ? "0dvl990alr4bb64w9b32dhzacvchpsspj8p3zqcgk7q5akvqh1mw"
, pkgs   ? import (builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
    inherit sha256; }) {
    config.allowUnfree = true;
    config.allowBroken = false;
  }
}:

let

coq-haskell = coqPackages:
  with pkgs.${coqPackages}; pkgs.stdenv.mkDerivation rec {
    name = "coq${coq.coq-version}-coq-haskell-${version}";
    version = "1.0";

    src = pkgs.fetchFromGitHub {
      owner  = "jwiegley";
      repo   = "coq-haskell";
      rev    = "08959da061eca867a3b09254960378d0450c501e";
      sha256 = "1ydd4708hzhn2vf8xlx8axc1pmm386ll0mvi94n7sgfxb90lz1pc";
    };

    buildInputs = [
      coq coq.ocaml coq.camlp5 coq.findlib pkgs.perl
    ];
    enableParallelBuilding = true;

    buildFlags = [
      "JOBS=$(NIX_BUILD_CORES)"
    ];

    installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

    env = pkgs.buildEnv { inherit name; paths = buildInputs; };
    passthru = {
      compatibleCoqVersions = v: builtins.elem v [ "8.11" "8.12" "8.13" "8.14" "8.15" ];
    };
  };

linearscan = coqPackages:
  with pkgs.${coqPackages}; pkgs.stdenv.mkDerivation rec {
    name = "coq${coq.coq-version}-linearscan-${version}";
    version = "1.0";

    src = if pkgs ? coqFilterSource
          then pkgs.coqFilterSource [] ./.
          else ./.;

    buildInputs = [
      coq coq.ocaml coq.camlp5 coq.findlib mathcomp (coq-haskell coqPackages)
    ];
    enableParallelBuilding = true;

    buildFlags = [
      "JOBS=$(NIX_BUILD_CORES)"
    ];

    installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

    env = pkgs.buildEnv { inherit name; paths = buildInputs; };
    passthru = {
      compatibleCoqVersions = v: builtins.elem v [ "8.11" "8.12" "8.13" "8.14" "8.15" ];
    };
  };

in {
  linearscan_8_11 = linearscan "coqPackages_8_11";
  linearscan_8_12 = linearscan "coqPackages_8_12";
  linearscan_8_13 = linearscan "coqPackages_8_13";
  linearscan_8_14 = linearscan "coqPackages_8_14";
  linearscan_8_15 = linearscan "coqPackages_8_15";
}
