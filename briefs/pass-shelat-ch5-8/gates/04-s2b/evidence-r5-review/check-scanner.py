"""Regression checks for R5-01's actual text-scanner false negative; run with python3 -I."""

from pathlib import Path
import re
import subprocess
import tempfile


root = Path.cwd()
gate = root / "briefs/pass-shelat-ch5-8/gates/04-s2b"
tool = gate / "evidence-r5/tools/scan.py"
old_rev = subprocess.check_output(["git", "rev-parse", "c39f0e11"], text=True).strip()
old_path = str(tool.relative_to(root))
cases = {
    "inline": ("  unfold TCSlib.Foreign.HiddenNat\n  exact 0\n", 1),
    "plain_multiline": ("  unfold\n    TCSlib.Foreign.HiddenNat\n  exact 0\n", 1),
    "comment_continuation": ("  unfold\n    -- explanation\n    TCSlib.Foreign.HiddenNat\n  exact 0\n", 1),
    "blank_continuation": ("  unfold\n\n    TCSlib.Foreign.HiddenNat\n  exact 0\n", 1),
    "nested_comment": ("  unfold\n    /- outer /- inner -/\n       comment -/\n    TCSlib.Foreign.HiddenNat\n  exact 0\n", 1),
    "delta_comment": ("  delta\n    -- explanation\n    TCSlib.Foreign.HiddenNat\n  exact 0\n", 1),
    "multiple_names": ("  unfold TCSlib.Foreign.HiddenNat\n\n    TCSlib.Foreign.OtherNat\n  exact 0\n", 2),
    "nth_rw": ("  nth_rw 1 [TCSlib.Foreign.HiddenNat]\n  exact 0\n", 1),
    "nth_rewrite": ("  nth_rewrite 1 [TCSlib.Foreign.HiddenNat]\n  exact 0\n", 1),
    "dedent_stops": ("  unfold Nat\n\n  exact 0\n    TCSlib.Foreign.HiddenNat\n", 0),
    "comment_ignored": ("  -- unfold TCSlib.Foreign.HiddenNat\n  exact 0\n", 0),
    "at_stops": ("  unfold Nat at h\n    TCSlib.Foreign.HiddenNat\n  exact 0\n", 0),
}

log = ["Pinned old scanner " + old_rev,
       "Text-parser regressions only; fixtures are not a new Lean execution audit."]
with tempfile.TemporaryDirectory(dir=root / ".lake/ps-maintainer") as directory:
    scratch = Path(directory)
    (scratch / "TCSlib").mkdir()
    (scratch / "candidates").mkdir()
    (scratch / "files.txt").write_text("TCSlib/Test.lean\n")
    (scratch / "constants.tsv").write_text(
        "TCSlib.Foreign.HiddenNat\tdef\tTCSlib.Foreign\n"
        "TCSlib.Foreign.OtherNat\tdef\tTCSlib.Foreign\n")
    (scratch / "seal.log").write_text("")
    old_tool = scratch / "old-scan.py"
    old_tool.write_text(subprocess.check_output(["git", "show", old_rev + ":" + old_path], text=True))
    (scratch / "declx.py").write_bytes((tool.parent / "declx.py").read_bytes())

    def run(scanner, body):
        source = "example : Nat := by\n" + body
        (scratch / "TCSlib/Test.lean").write_text(source)
        output = scratch / "scan.log"
        subprocess.run([
            "python3", "-I", str(scanner), str(scratch), str(scratch / "files.txt"),
            str(scratch / "constants.tsv"), str(scratch / "candidates"),
            str(scratch / "seal.log"), str(output),
        ], check=True, capture_output=True, text=True)
        text = output.read_text()
        count = int(re.search(r"lemma-list hits: (\d+)", text).group(1))
        for line in text.splitlines():
            if line.startswith("TCSlib/Test.lean:"):
                number = int(line.split("\t")[0].rsplit(":", 1)[1])
                assert "TCSlib.Foreign." in source.splitlines()[number - 1], (number, source)
        return count

    before = run(old_tool, cases["comment_continuation"][0])
    assert before == 0
    log.append("REPRODUCED: old scanner misses comment-only unfold continuation (0 hits).")
    for name, (body, expected) in cases.items():
        actual = run(tool, body)
        assert actual == expected, (name, actual, expected)
        log.append(f"PASS {name}: {actual} hits, expected {expected}; hit line numbers checked")
log.append(f"PASS {len(cases)} cases")
(gate / "evidence-r5-review/scanner-regressions.log").write_text("\n".join(log) + "\n")
print("\n".join(log))
