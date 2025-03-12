# Copyright (c) 2025 The mldsa-native project authors
# SPDX-License-Identifier: Apache-2.0

# ACVP client for ML-DSA
#
# Processes 'internalProjection.json' files from
# https://github.com/usnistgov/ACVP-Server/blob/master/gen-val/json-files
#
# Invokes `acvp_mldsa{lvl}` under the hood.

import os
import json
import sys
import subprocess

# Check if we need to use a wrapper for execution (e.g. QEMU)
exec_prefix = os.environ.get("EXEC_WRAPPER", "")
exec_prefix = [exec_prefix] if exec_prefix != "" else []

acvp_dir = "test/acvp_data"
acvp_keygen_json = f"{acvp_dir}/acvp_keygen_internalProjection.json"
acvp_sigGen_json = f"{acvp_dir}/acvp_sigGen_internalProjection.json"
acvp_sigVer_json = f"{acvp_dir}/acvp_sigVer_internalProjection.json"

with open(acvp_keygen_json, "r") as f:
    acvp_keygen_data = json.load(f)

with open(acvp_sigGen_json, "r") as f:
    acvp_sigGen_data = json.load(f)

with open(acvp_sigVer_json, "r") as f:
    acvp_sigVer_data = json.load(f)


def err(msg, **kwargs):
    print(msg, file=sys.stderr, **kwargs)


def info(msg, **kwargs):
    print(msg, **kwargs)


def get_acvp_binary(tg):
    """Convert JSON dict for ACVP test group to suitable ACVP binary."""
    parameterSetToLevel = {
        "ML-DSA-44": 44,
        "ML-DSA-65": 65,
        "ML-DSA-87": 87,
    }
    level = parameterSetToLevel[tg["parameterSet"]]
    basedir = f"./test/build/mldsa{level}/bin"
    acvp_bin = f"acvp_mldsa{level}"
    return f"{basedir}/{acvp_bin}"


def run_keyGen_test(tg, tc):
    info(f"Running keyGen test case {tc['tcId']} ... ", end="")
    acvp_bin = get_acvp_binary(tg)
    assert tg["testType"] == "AFT"
    acvp_call = exec_prefix + [
        acvp_bin,
        "keyGen",
        f"seed={tc['seed']}",
    ]
    result = subprocess.run(acvp_call, encoding="utf-8", capture_output=True)
    if result.returncode != 0:
        err("FAIL!")
        err(f"{acvp_call} failed with error code {result.returncode}")
        err(result.stderr)
        exit(1)
    # Extract results and compare to expected data
    for l in result.stdout.splitlines():
        (k, v) = l.split("=")
        if v != tc[k]:
            err("FAIL!")
            err(f"Mismatching result for {k}: expected {tc[k]}, got {v}")
            exit(1)
    info("OK")


def run_sigGen_test(tg, tc):
    info(f"Running sigGen test case {tc['tcId']} ... ", end="")
    acvp_bin = get_acvp_binary(tg)

    assert tg["testType"] == "AFT"

    # TODO: implement pre-hashing mode
    if tg["preHash"] != "pure":
        info("SKIP preHash")
        return

    # TODO: implement internal interface
    if tg["signatureInterface"] != "external":
        info("SKIP internal")
        return

    # TODO: implement external-mu mode
    if tg["externalMu"] is True:
        info("SKIP externalMu")
        return

    # TODO: probably we want to handle handle the deterministic case differently
    if tg["deterministic"] is True:
        tc["rnd"] = "0" * 64

    assert tc["hashAlg"] == "none"
    assert len(tc["context"]) <= 2 * 255
    assert len(tc["message"]) <= 2 * 65536

    acvp_call = exec_prefix + [
        acvp_bin,
        "sigGen",
        f"message={tc['message']}",
        f"rnd={tc['rnd']}",
        f"sk={tc['sk']}",
        f"context={tc['context']}",
    ]
    result = subprocess.run(acvp_call, encoding="utf-8", capture_output=True)
    if result.returncode != 0:
        err("FAIL!")
        err(f"{acvp_call} failed with error code {result.returncode}")
        err(result.stderr)
        exit(1)
    # Extract results and compare to expected data
    for l in result.stdout.splitlines():
        (k, v) = l.split("=")
        if v != tc[k]:
            err("FAIL!")
            err(f"Mismatching result for {k}: expected {tc[k]}, got {v}")
            exit(1)
    info("OK")


def run_sigVer_test(tg, tc):
    info(f"Running sigVer test case {tc['tcId']} ... ", end="")
    acvp_bin = get_acvp_binary(tg)

    # TODO: implement pre-hashing mode
    if tg["preHash"] != "pure":
        info("SKIP preHash")
        return

    # TODO: implement internal interface
    if tg["signatureInterface"] != "external":
        info("SKIP internal")
        return

    # TODO: implement external-mu mode
    if tg["externalMu"] is True:
        info("SKIP externalMu")
        return

    assert tc["hashAlg"] == "none"
    assert len(tc["context"]) <= 2 * 255
    assert len(tc["message"]) <= 2 * 65536

    acvp_call = exec_prefix + [
        acvp_bin,
        "sigVer",
        f"message={tc['message']}",
        f"context={tc['context']}",
        f"signature={tc['signature']}",
        f"pk={tc['pk']}",
    ]
    result = subprocess.run(acvp_call, encoding="utf-8", capture_output=True)

    if (result.returncode == 0) != tc["testPassed"]:
        err("FAIL!")
        err(
            f"Mismatching verification result: expected {tc['testPassed']}, got {result.returncode == 0}"
        )
        exit(1)
    info("OK")


for tg in acvp_keygen_data["testGroups"]:
    for tc in tg["tests"]:
        run_keyGen_test(tg, tc)

for tg in acvp_sigGen_data["testGroups"]:
    for tc in tg["tests"]:
        run_sigGen_test(tg, tc)

for tg in acvp_sigVer_data["testGroups"]:
    for tc in tg["tests"]:
        run_sigVer_test(tg, tc)
