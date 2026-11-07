"""Candidate enumeration for gates 106/114/115, including active/prepared/delivery refs.

This is a source search, not an exhaustive duplication proof. The gate's
scope note classifies candidates and the copy-text screen is a separate run.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
import re
import subprocess


RECORDS = Path(__file__).resolve().parents[3]
SCRATCH = Path(os.environ["TCSLIB_SCRATCH"])


def git(*args: str) -> str:
    return subprocess.check_output(["git", "-C", str(RECORDS), *args], text=True).strip()


def main() -> None:
    summary = json.loads((SCRATCH / "gate-source-exports/summary.json").read_text())
    refs = ["origin/complexity/arora-barak-ch3-4", "origin/lean/dedup-sg1",
            "origin/lean/dedup-natbits", "origin/lean/epad-padding-fill",
            "origin/pr/215", "origin/pr/222", "origin/pr/228"]
    refs.extend(data["head"] for data in summary.values())
    available = git("for-each-ref", "--format=%(refname)", "refs/heads", "refs/remotes/origin",
                    "refs/deliver", "refs/local").splitlines()
    refs.extend(ref for ref in available if re.search(r"/(deliver/|local/[^\n]*landing|lean/dedup-ro1$)", ref))
    checked = {}
    for ref in dict.fromkeys(refs):
        sha = git("rev-parse", ref)
        subprocess.run(["git", "-C", str(RECORDS), "cat-file", "-e", sha + "^{commit}"], check=True)
        checked[ref] = sha
    names = r"length_bits_eq_log|lt_two_pow_bits|two_pow_bits_le_two_mul_add_one|ofDigits_lt_two_pow"
    shapes = r"(theorem|lemma).*(length_bits|bitsVal_lt_two_pow|word_lt|bits_succ_le|two_pow_bits|bits_length)"
    for gate, data in summary.items():
        output = RECORDS / "campaign/gates" / gate / "evidence/current/search"
        output.mkdir(parents=True, exist_ok=True)
        (output / "refs.json").write_text(json.dumps(checked, indent=2) + "\n")
        if gate.startswith(("114", "115")):
            names = r"length_bits_eq_log|lt_two_pow_bits|two_pow_bits_le_two_mul_add_one|ofDigits_lt_two_pow"
            shapes = r"(theorem|lemma).*(length_bits|bitsVal_lt_two_pow|word_lt|bits_succ_le|two_pow_bits|bits_length)"
            if gate.startswith("115"):
                names = r"epad_|mem_SPACE_padLang|two_pow_bits_le|length_bits_le_self"
                shapes = r"(theorem|lemma).*(scan_loop|mul_loop|pow_loop|ones_loop|val_run|bitsVal_lt_two_pow)"
            with (output / "names-and-shapes.txt").open("w") as log:
                for sha in dict.fromkeys(checked.values()):
                    labels = [ref for ref, value in checked.items() if value == sha]
                    log.write("\nREFS " + ", ".join(labels) + "\n")
                    for pattern in (names, shapes):
                        proc = subprocess.run(
                            ["git", "-C", str(RECORDS), "grep", "-n", "-E", pattern,
                             sha, "--", "TCSlib"], text=True, stdout=log, stderr=subprocess.STDOUT)
                        assert proc.returncode in (0, 1)
            patterns = {
                "size-and-log-readings": r"Nat\.(size_eq_bits_len|size_le|lt_size|size_pos|pow_log_le_self)|Nat\.log 2.*\+ 1",
                "word-value-readings": r"Nat\.ofDigits_lt_base_pow_length|bitsVal_lt_two_pow|ofDigits_lt_two_pow",
                "length-bound-readings": r"(bits|size).*length.*(≤|<|=)|(≤|<|=).*2 \^.*bits.*length",
            }
            if gate.startswith("115"):
                patterns["loop-contract-candidates"] = r"(theorem|lemma|def).*(scan_loop|mul_loop|pow_loop|ones_loop|ARMLoops)"
        else:
            patterns = {
                "retired-concatenation-names": r"counter_span_append|tautDual_segment_add|dgSpan_add",
                "segment-helper-candidates": r"(private )?(lemma|theorem|def).*([Ss]egment|[Ss]pan|guard_add|splitSafe)",
                "run-concatenation-steps": r"runFrom_add|exists_eq_add_of_le|runFrom_of_halt",
            }
        for label in ("base", "head"):
            tree = Path(data[label + "_export"])
            for kind, pattern in patterns.items():
                regex = re.compile(pattern)
                hits = []
                for path in sorted((tree / "TCSlib").rglob("*.lean")):
                    for number, line in enumerate(path.read_text().splitlines(), 1):
                        if regex.search(line):
                            hits.append(f"{path.relative_to(tree)}:{number}:{line}")
                (output / f"{kind}-{label}.txt").write_text("\n".join(hits) + ("\n" if hits else ""))
        print(gate, "searched", len(checked), "refs;", len(set(checked.values())), "distinct trees", flush=True)


if __name__ == "__main__":
    main()
