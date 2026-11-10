"""Check the one adapter module; preserve every attempted source and raw log."""

from pathlib import Path
import subprocess
import sys


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
MODULE = "TCSlib/Cryptography/Encoding/BinaryArith"


def main():
    evidence = HERE / "evidence"
    development = evidence / "development"
    development.mkdir(parents=True, exist_ok=True)
    number = len(list(development.iterdir()))
    output = development / f"{number:02d}"
    output.mkdir()
    (output / "source.lean").write_bytes((ROOT / (MODULE + ".lean")).read_bytes())
    order = evidence / "development-module-order.txt"
    order.write_text(MODULE + "\n")
    driver = ROOT / "briefs/lwe-sis-constructions/gates/04-encoding-adapters/check_modules.py"
    result = subprocess.run([
        sys.executable, "-I", str(driver), "--order", str(order),
        "--output", str(output),
        "--oleans", str(ROOT / ".lake/adapter-final-2-oleans"),
    ], cwd=ROOT)
    raise SystemExit(result.returncode)


if __name__ == "__main__":
    main()
