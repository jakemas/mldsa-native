# Copyright (c) The mlkem-native project authors
# Copyright (c) The mldsa-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
{ stdenv, fetchFromGitHub, writeText, ... }:
stdenv.mkDerivation rec {
  pname = "s2n_bignum";
  # Pinned to https://github.com/awslabs/s2n-bignum/pull/410
  # (jakemas:add-vpabsd-vptest) which adds VPABSD and VPTEST instruction
  # models required by the poly_chknorm_avx2_asm HOL-Light proof.
  # Once that PR merges, this can move back to upstream awslabs/s2n-bignum.
  version = "4414a110250cea1c02ffe71d031c1254ba788ec0";
  src = fetchFromGitHub {
    owner = "jakemas";
    repo = "s2n-bignum";
    rev = "${version}";
    hash = "sha256-dbgC4d+LT3Tbrz2Q/QtT5QFu2B/N6dNghPKwki1IgfQ=";
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
