# This file was auto-generated by cabal2nix. Please do NOT edit manually!

{ cabal, hoopl, hspec, hspecExpectations, HUnit, transformers, free }:

cabal.mkDerivation (self: {
  pname = "linearscan";
  version = "0.1.0.0";
  src = builtins.filterSource (path: type: type != "unknown") ./.;
  buildDepends = [ transformers ];
  testDepends = [ hoopl hspec hspecExpectations HUnit transformers free ];
  meta = {
    homepage = "http://github.com/jwiegley/linearscan";
    description = "An optimized linear scan register allocator";
    license = self.stdenv.lib.licenses.bsd3;
    platforms = self.ghc.meta.platforms;
  };
})
