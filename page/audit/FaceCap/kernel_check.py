#!/usr/bin/env python3
"""Replay the FaceCap exhaustive certificate using ordinary Lean kernel reduction.

Run from any directory with Python 3.9+ and the project's lake in PATH.
Examples:
    python3 audit/FaceCap/kernel_check.py --stop 8 --chunk-size 4
    python3 audit/FaceCap/kernel_check.py --jobs 2

The default interval is all 4096 masks. The full replay uses appreciable CPU
time. Each concurrent worker runs a separate Lean process. Generated sources
and .olean files are temporary; the original module is never edited.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import os
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory


PROJECT = Path(__file__).resolve().parents[2]
TOTAL = 4096
NS = "Page.FaceCap"


def lake_env(*args):
    return subprocess.check_output(["lake", "env", *args], cwd=PROJECT, text=True).strip()


def range_name(lo, hi):
    return f"range{lo}to{hi}"


def range_header(lo, hi):
    return (
        f"theorem {range_name(lo, hi)} (i : Fin 4096) "
        f"(low : {lo} ≤ i.val) (high : i.val < {hi}) : AuditCase i := by\n"
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--start", type=int, default=0, help="first mask, inclusive")
    parser.add_argument("--stop", type=int, default=TOTAL, help="last boundary, exclusive")
    parser.add_argument("--chunk-size", type=int, default=32)
    parser.add_argument("--jobs", type=int, default=1)
    args = parser.parse_args()
    if not 0 <= args.start < args.stop <= TOTAL or min(args.chunk_size, args.jobs) < 1:
        parser.error("use 0 ≤ start < stop ≤ 4096 and positive chunk-size and jobs")

    # Use the actual module's statement and proofs so that a successful full
    # run also kernel-checks the rotation encoding and transfer to all fittings.
    source = (PROJECT / "Page/FaceCap.lean").read_text()
    intro, cert = source.split("/-- The independent checks include", 1)
    _, cert = cert.split("private theorem audit : ∀ i : Fin 4096, ", 1)
    statement, remainder = cert.split(" := by native_decide", 1)
    intro = intro.replace("private def encode ", "def encode ")
    shared = (
        f"{intro}\ndef AuditCase (i : Fin 4096) : Prop := {statement}\n"
        "instance (i : Fin 4096) : Decidable (AuditCase i) := by\n"
        "  unfold AuditCase; infer_instance\n"
        f"end {NS}\n"
    )

    subprocess.run(["lake", "build", "Page.HoGLocal"], cwd=PROJECT, check=True)
    lean = Path(lake_env("lean", "--print-prefix")) / "bin/lean"
    search = [str((PROJECT / p).resolve()) for p in lake_env("printenv", "LEAN_PATH").split(os.pathsep) if p]
    pieces = [(a, min(a + args.chunk_size, args.stop)) for a in range(args.start, args.stop, args.chunk_size)]

    with TemporaryDirectory(prefix="page-face-cap-") as tmp:
        temp = Path(tmp)
        env = dict(os.environ, LEAN_PATH=os.pathsep.join([tmp, *search]))

        def compile_module(name, text):
            (temp / f"{name}.lean").write_text(text)
            subprocess.run([lean, "-o", f"{name}.olean", f"{name}.lean"], cwd=temp, env=env, check=True)

        compile_module("KernelShared", shared)

        def check_piece(bounds):
            lo, hi = bounds
            name = f"Chunk{lo}to{hi}"
            length = hi - lo
            checked = (
                f"private theorem checked : ∀ j : Fin {length}, "
                f"AuditCase ⟨{lo} + j.val, by omega⟩ := by decide +kernel\n"
            )
            theorem = (
                range_header(lo, hi)
                + f"  let j : Fin {length} := ⟨i.val - {lo}, by omega⟩\n"
                + f"  have eq : (⟨{lo}+j.val, by omega⟩ : Fin 4096) = i := "
                + "Fin.ext (by dsimp [j]; omega)\n"
                + "  exact eq ▸ checked j\n"
            )
            compile_module(name, f"import KernelShared\nnamespace {NS}\n"
                           f"set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n"
                           f"{checked}{theorem}end {NS}\n")
            print(f"Kernel checked masks [{lo}, {hi})", flush=True)
            return f"import {name}\n"

        with ThreadPoolExecutor(max_workers=args.jobs) as workers:
            imports = "".join(workers.map(check_piece, pieces))

        # Recombine adjacent interval theorems with ordinary proofs. Lean
        # checks the coverage and arithmetic, including both boundary masks.
        proof = [imports, f"namespace {NS}\n"]
        ranges = pieces
        while len(ranges) > 1:
            merged = []
            for k in range(0, len(ranges), 2):
                lo, mid = ranges[k]
                if k + 1 == len(ranges):
                    merged.append((lo, mid))
                    continue
                next_lo, hi = ranges[k + 1]
                assert mid == next_lo
                proof.extend([range_header(lo, hi), f"  by_cases side : i.val < {mid}\n",
                              f"  · exact {range_name(lo, mid)} i low side\n",
                              f"  · exact {range_name(mid, hi)} i (by omega) high\n"])
                merged.append((lo, hi))
            ranges = merged

        name = range_name(args.start, args.stop)
        proof.append(f"#print axioms {name}\n")
        if (args.start, args.stop) == (0, TOTAL):
            proof.append("private theorem audit (i : Fin 4096) : AuditCase i := "
                         f"{name} i (Nat.zero_le _) i.isLt\n")
            proof.append(remainder)
            for suffix in ["all_fittings", "capped_bound", "witnesses"]:
                proof.append(f"\n#print axioms {NS}.{suffix}\n")
        else:
            proof.append(f"end {NS}\n")
        compile_module("KernelResult", "".join(proof))
        print(f"Verified {args.stop - args.start} masks on [{args.start}, {args.stop}).", flush=True)


if __name__ == "__main__":
    main()
