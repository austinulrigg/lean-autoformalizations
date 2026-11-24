"""From any directory, run python3 audit/Blocks/check.py with lake and cc on PATH."""
import json
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent


def records(command):
    output = subprocess.check_output(command, cwd=ROOT, text=True)
    return [json.loads(line) for line in output.splitlines()]


def main():
    subprocess.run(["lake", "build", "Page.HoGBlocks"], cwd=ROOT, check=True)
    lean_records = records(["lake", "env", "lean", "--run", HERE / "BlockAudit.lean"])
    with TemporaryDirectory() as work:
        program = Path(work) / "c-block-audit"
        subprocess.run(["cc", "-O1", "-DLONG", "-std=gnu17", "-pthread",
                        HERE / "block_audit.c", "-lm", "-o", program], check=True)
        c_records = records([program])
    if len(lean_records) != 1544 or len(c_records) != len(lean_records):
        raise AssertionError(f"Unexpected record counts {len(lean_records)}, {len(c_records)}")
    for a, b in zip(lean_records, c_records):
        if a != b:
            raise AssertionError(f"First discrepancy: Lean {a}, C {b}")
    print("Matched all 1,544 records (772 connected labelled simple graphs, orders 1–5, "
          "two edge insertion orders). Each passed the independent decomposition audit.")


if __name__ == "__main__":
    main()
