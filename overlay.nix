final: prev:
let
  callCabal2nix = prev.haskellPackages.callCabal2nix;
  source-ignores = [ "*.nix" "result" ];
  source = path: prev.nix-gitignore.gitignoreSource source-ignores path;
in
{
  haskellPackages = prev.haskellPackages.override {
    overrides = selfH: superH: with prev.haskell.lib; {

      # TODO try allowing tests for transitive deps (be sure to disable tests for LH)
      #mkDerivation = args: superH.mkDerivation (
      #  args // { doCheck = false; doHaddock = false; jailbreak = true; enableLibraryProfiling = false; }
      #);

      # LH without tests
      liquidhaskell =
        let src = prev.nix-gitignore.gitignoreSource ([ "liquid-*" ] ++ source-ignores) ./.;
        in dontCheck (callCabal2nix "liquidhaskell" src { });
      ## LH spec/shadow packages
      liquid-base = dontHaddock (callCabal2nix "liquid-base" (source ./liquid-base) { });
      liquid-bytestring = dontHaddock (callCabal2nix "liquid-bytestring" (source ./liquid-bytestring) { });
      liquid-containers = (callCabal2nix "liquid-containers" (source ./liquid-containers) { });
      liquid-ghc-prim = dontHaddock (callCabal2nix "liquid-ghc-prim" (source ./liquid-ghc-prim) { });
      liquid-parallel = (callCabal2nix "liquid-parallel" (source ./liquid-parallel) { });
      liquid-vector = (callCabal2nix "liquid-vector" (source ./liquid-vector) { });
      ## LH bundles
      liquid-platform = (callCabal2nix "liquid-platform" (source ./liquid-platform) { });
      liquid-prelude = dontHaddock (callCabal2nix "liquid-prelude" (source ./liquid-prelude) { });
      ## LH with tests
      liquidhaskell_with_tests = overrideCabal selfH.liquidhaskell (old: {
        testDepends = old.testDepends or [ ] ++ [ prev.hostname ];
        #testHaskellDepends = old.testHaskellDepends ++ projectPackages; #FIXME move this overlay into the flake to access the list
        preCheck = ''export TASTY_LIQUID_RUNNER="liquidhaskell -v0"'';
      });

    };
  };
}
