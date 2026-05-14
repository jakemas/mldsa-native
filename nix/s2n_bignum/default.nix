# Copyright (c) The mlkem-native project authors
# Copyright (c) The mldsa-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
{ stdenv, fetchFromGitHub, writeText, ... }:
stdenv.mkDerivation rec {
  pname = "s2n_bignum";
  version = "0c5ae1ae061e5664aace76013750bad56c223678";
  src = fetchFromGitHub {
    owner = "jakemas";
    repo = "s2n-bignum";
    rev = "${version}";
    hash = "sha256-c0wdKXi8Cda8X1Q3R2grL+dkOhf4ImDda1Zr2VZuhHo=";
  };
  setupHook = writeText "setup-hook.sh" ''
    export S2N_BIGNUM_DIR="$1"
  '';
  patches = [ ];
  dontBuild = true;
  installPhase = ''
    mkdir -p $out
    cp -a . $out/
  '';
}
