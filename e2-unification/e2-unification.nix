{ mkDerivation, array, base, Cabal, cabal-doctest, containers
, doctest, Glob, lib, logict, mtl, QuickCheck, template-haskell
}:
mkDerivation {
  pname = "e2-unification";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = true;
  isExecutable = true;
  setupHaskellDepends = [ base Cabal cabal-doctest ];
  libraryHaskellDepends = [ array base containers logict mtl ];
  executableHaskellDepends = [ array base containers logict mtl ];
  testHaskellDepends = [
    array base containers doctest Glob logict mtl QuickCheck
    template-haskell
  ];
  homepage = "https://github.com/fizruk/e2-unification#readme";
  license = lib.licenses.bsd3;
}
