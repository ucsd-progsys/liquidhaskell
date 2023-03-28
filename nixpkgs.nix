let
  # NixOS/Nixpkgs master 2022-11-27
  rev = "a115bb9bd56831941be3776c8a94005867f316a7";
  sha256 = "1501jzl4661qwr45b9ip7c7bpmbl94816draybhh60s9wgxn068d";
in
import (fetchTarball {
  inherit sha256;
  url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
})
