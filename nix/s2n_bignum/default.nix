# Copyright (c) The mlkem-native project authors
# Copyright (c) The mldsa-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
{ stdenv, fetchFromGitHub, writeText, ... }:
stdenv.mkDerivation rec {
  pname = "s2n_bignum";
  version = "eb5843f1898c13ec0285cddd87e84ec9c715d5c8";
  src = fetchFromGitHub {
    owner = "awslabs";
    repo = "s2n-bignum";
    rev = "${version}";
    hash = "sha256-k1MZnJizvxh8JZ9CV0xtOOPG1nwBMx/wmm5UzpN9Hys=";
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
