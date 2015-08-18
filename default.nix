{ mkDerivation, base, containers, mtl, stdenv, transformers }:
mkDerivation {
  pname = "linearscan";
  version = "0.8.0";
  src = ./.;
  buildDepends = [ base containers mtl transformers ];
  homepage = "http://github.com/jwiegley/linearscan";
  description = "Linear scan register allocator, formally verified in Coq";
  license = stdenv.lib.licenses.bsd3;
}
