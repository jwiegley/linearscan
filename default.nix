args@{
  rev    ? "41cc1d5d9584103be4108c1815c350e07c807036"
, sha256 ? "1zwbkijhgb8a5wzsm1dya1a4y79bz6di5h49gcmw6klai84xxisv"

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
      rev    = "347555e0f89c5729f81b18a881399ccdc79d7cb6";
      sha256 = "15n02zhi0w6iyqsbzqayfad3vhp5pnh2ny345dyqk30zk91ggk5n";
    };

    buildInputs = [
      coq coq.ocaml coq.camlp5 coq.findlib pkgs.perl
    ];
    enableParallelBuilding = true;

    installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

    env = pkgs.buildEnv { inherit name; paths = buildInputs; };
    passthru = {
      compatibleCoqVersions = v: builtins.elem v [ "8.14" "8.15" ];
    };
  };

coq-linearscan = coqPackages:
  with pkgs.${coqPackages}; pkgs.stdenv.mkDerivation rec {
    name = "coq${coq.coq-version}-linearscan-${version}";
    version = "1.1.0";

    src = if pkgs ? coqFilterSource
          then pkgs.coqFilterSource [] ./.
          else ./.;

    buildInputs = [
      coq coq.ocaml coq.camlp5 coq.findlib mathcomp (coq-haskell coqPackages)
    ];
    enableParallelBuilding = true;

    installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

    env = pkgs.buildEnv { inherit name; paths = buildInputs; };
    passthru = {
      compatibleCoqVersions = v: builtins.elem v [ "8.14" "8.15" ];
    };
  };

in {
  coq-linearscan_8_14 = coq-linearscan "coqPackages_8_14";
  coq-linearscan_8_15 = coq-linearscan "coqPackages_8_15";
}
