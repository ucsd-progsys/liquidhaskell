{ pkgs ?  import ./nixpkgs.nix {}
, ghc ? pkgs.haskell.compiler.ghc8107
}:

with pkgs;

haskell.lib.buildStackProject ({
  name = "stitch-lh";
  buildInputs = [ git z3 ];
  ghc = ghc;
  LANG = "en_US.utf8";
})
