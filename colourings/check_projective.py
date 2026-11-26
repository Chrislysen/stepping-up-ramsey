#!/usr/bin/env python3
"""Compile once and check the projective witness in this directory.

Run: python3 check_projective.py
Requires Python 3 and g++ or clang++ with C++17 support; no Python packages.
"""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


CASES = [
    ("R574_858_points_rule.json", 857, [5, 7],
     "d5c58d63c0b8320ab89fb4cc76345856b0aa4529c1db653275dc11f181bdd376",
     365085, 22110642855, 22111007940),
]


def main():
    folder = Path(__file__).resolve().parent
    compiler = shutil.which("g++") or shutil.which("clang++")
    if not compiler:
        raise SystemExit("Install g++ or clang++ with C++17 support and try again.")
    with tempfile.TemporaryDirectory() as work:
        executable = Path(work) / ("verify.exe" if os.name == "nt" else "verify")
        subprocess.run([
            compiler, "-O3", "-std=c++17", "-Wall", "-Wextra", "-pedantic",
            str(folder / "verify_projective.cpp"), "-o", str(executable),
        ], check=True)
        for name, q, sizes, digest, count_a, count_b, distinct in CASES:
            witness = json.loads((folder / name).read_text(encoding="utf-8"))
            if (witness["q"], witness["points"], witness["uniformity"], witness["sizes"]) != (
                q, q + 1, 4, sizes
            ):
                raise SystemExit(name + ": witness parameters do not match the claim.")
            table = witness["table"]
            if (hashlib.sha256(table.encode("ascii")).hexdigest() != digest
                    or witness["table_sha256"] != digest):
                raise SystemExit(name + ": table does not match the manuscript digest.")
            run = subprocess.run([
                str(executable), str(q), table, str(sizes[0]), str(sizes[1]),
            ], check=True, text=True, capture_output=True)
            result = json.loads(run.stdout)
            expected = {
                "q": q, "n": q + 1, "sizes": sizes,
                "mode": "PGL_normalized_0_1_infinity",
                "sets_size_A": count_a, "sets_size_B": count_b,
                "distinct_sets_visited": distinct,
                "forbidden_color0": 0, "forbidden_color1": 0, "pass": True,
            }
            if any(result.get(key) != value for key, value in expected.items()):
                raise SystemExit(name + ": unexpected check result: " + run.stdout)
            print(json.dumps({"file": name, **result}), flush=True)
    print("PASS: the projective witness, its table hash and the normalized counts.")


if __name__ == "__main__":
    main()
