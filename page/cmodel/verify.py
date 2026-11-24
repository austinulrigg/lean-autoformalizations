"""Regenerate the upstream GOTO model and check the C properties using CBMC 6.11.0."""
from hashlib import sha256
from pathlib import Path
import re
import subprocess
from tempfile import TemporaryDirectory

ROOT = Path(__file__).resolve().parents[1]
DIGEST = "f032b259c5efff9c92f43108887bcd90ff56fc95afa950d80452a5b97a9a0513"
PROPERTIES = {"degree_switch": 1, "within_word": 14, "small_components": 14, "lower_bound": 1}

def main():
    if sha256((ROOT / "upstream/genus.c").read_bytes()).hexdigest() != DIGEST:
        raise SystemExit("The upstream source differs from the pinned revision.")
    print(subprocess.check_output(["cbmc", "--version"], text=True).strip(), flush=True)
    with TemporaryDirectory() as build:
        for source, model in [("upstream/genus.c", "hog.goto"), ("cmodel/checks.c", "checks.goto")]:
            subprocess.run(["goto-cc", "-DLONG", "-std=gnu17", "-pthread", source,
                            "-lm", "-o", str(Path(build) / model)], cwd=ROOT, check=True)
        table = subprocess.check_output(["goto-instrument", "--list-goto-functions",
                                        str(Path(build) / "hog.goto")], text=True)
        for name in ("main", "ph_page_run", "hog_run_page_direct", "hog_run_page_low_mem_direct",
                     "hog_biconnected_blocks", "hog_run_graph"):
            if not re.search(r"^.*?/\* " + name + r" \*/$", table, re.MULTILINE):
                raise RuntimeError(f"Missing function body: {name}")
        print("Rebuilt the full C translation unit and found both PAGE entry points and the dispatcher.")
        for name, bound in PROPERTIES.items():
            result = subprocess.run(["cbmc", str(Path(build) / "checks.goto"), "--function",
                    f"check_{name}", "--unwind", str(bound), "--unwinding-assertions",
                    "--object-bits", "12", "--slice-formula", "--verbosity", "5"],
                    cwd=ROOT, capture_output=True, text=True)
            assertions = [s for s in result.stdout.splitlines()
                          if s.startswith(f"[check_{name}.assertion.")]
            if result.returncode or "VERIFICATION SUCCESSFUL" not in result.stdout or not assertions:
                raise RuntimeError(result.stderr + "\n" + result.stdout[-5000:])
            print("\n".join(assertions), flush=True)
    print("All four harnesses passed.")

if __name__ == "__main__":
    main()
