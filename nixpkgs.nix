let
  rev = "0cbe9f69c234a7700596e943bfae7ef27a31b735";
  sha256 = "15znwycfmbdcccqgld97x6375s5j028v6zmgvvr811dbny7cgy4c";
in
import (fetchTarball {
  inherit sha256;
  url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
})
