"""Widths and hygiene of the U2 unit's landed files (read-only; standard library only).

Usage: python3 -I hygiene.py <base root> <landed root>

For each landed file: lines not present verbatim in its base version (all lines, for the new
module) are at most 100 characters; UTF-8, LF line ends, one final newline, no tab, no trailing
whitespace on new or changed lines, no `#`-command at column 0, the three standard `set_option` lines. Exit 1 on failure.
"""
import os
import re
import sys

FILES = ["TCSlib/Complexity/TuringMachine/Build/StepBlockLoop.lean",
         "TCSlib/Complexity/TuringMachine/Codes2Tape.lean",
         "TCSlib/Complexity/TuringMachine/UniversalK.lean",
         "TCSlib/Complexity/TuringMachine/SelfUniversal.lean",
         "TCSlib/Complexity/TuringMachine.lean"]
OPTS = ["set_option maxHeartbeats 0", "set_option relaxedAutoImplicit false",
        "set_option autoImplicit false"]
base_root, land_root = sys.argv[1:3]
fail = []
print("| file | lines | max width | new or changed lines over 100 | hygiene |")
print("|---|---|---|---|---|")
for rel in FILES:
    raw = open(os.path.join(land_root, rel), "rb").read()
    text = raw.decode("utf-8")
    lines = text.split("\n")
    bp = os.path.join(base_root, rel)
    blines = set(open(bp, encoding="utf-8").read().split("\n")) if os.path.isfile(bp) else set()
    wide = [i + 1 for i, l in enumerate(lines) if len(l) > 100 and l not in blines]
    checks = {"CR": b"\r" not in raw, "final newline": text.endswith("\n") and not
              text.endswith("\n\n"), "tab": "\t" not in text,
              "trailing space (new lines)": all(l == l.rstrip() for l in lines
                                                if l not in blines),
              "#-command": not any(re.match(r"#[a-z]", l) for l in lines),
              "options": all(o in lines for o in OPTS) or rel.endswith("TuringMachine.lean")}
    bad = [k for k, v in checks.items() if not v]
    if wide:
        fail.append(f"{rel}: wide lines {wide}")
    if bad:
        fail.append(f"{rel}: {bad}")
    print(f"| `{rel}` | {len(lines) - 1} | {max(len(l) for l in lines)} | "
          f"{wide if wide else 'none'} | {'ok' if not bad else bad} |")
print()
if fail:
    print("WIDTHS/HYGIENE: FAIL — " + "; ".join(fail))
    sys.exit(1)
print("WIDTHS/HYGIENE: PASS")
