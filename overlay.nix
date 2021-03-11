final: prev:
let
  callCabal2nix = prev.haskellPackages.callCabal2nix;
  source = path: prev.nix-gitignore.gitignoreSource [ ] path;
in
{
  haskellPackages = prev.haskellPackages.override {
    overrides = selfH: superH: {

      # TODO try allowing tests for transitive deps (be sure to disable tests for LH)
      #mkDerivation = args: superH.mkDerivation (
      #  args // { doCheck = false; doHaddock = false; jailbreak = true; enableLibraryProfiling = false; }
      #);

      liquidhaskell = prev.haskell.lib.dontCheck (callCabal2nix
        "liquidhaskell"
        (prev.nix-gitignore.gitignoreSource [ "liquid-*" ] ./.)
        { });

    };
  };
}
