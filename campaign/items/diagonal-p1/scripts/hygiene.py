"""Widths and hygiene of the landed Diagonal.lean (read-only; standard library only).

Usage: python3 -I hygiene.py <base Diagonal.lean> <landed Diagonal.lean>

Widths: every line of the landed file is at most 100 characters (code points), except lines
present verbatim in the base file. Hygiene: UTF-8, LF line ends, a final newline, no tab, no
trailing whitespace, no `#`-command (`#check`, `#eval`, `#print`, …) at column 0, no
`set_option` other than the base file's, no new `private` declaration. Exit 1 on any failure.
"""
import re
import sys

base_b = open(sys.argv[1], "rb").read()
land_b = open(sys.argv[2], "rb").read()
fail = []
try:
    land = land_b.decode("utf-8")
    base = base_b.decode("utf-8")
except UnicodeDecodeError as e:
    print(f"HYGIENE: FAIL — not UTF-8: {e}")
    sys.exit(1)
blines, llines = set(base.split("\n")), land.split("\n")
wide = [(i + 1, len(l)) for i, l in enumerate(llines) if len(l) > 100]
new_wide = [(i, w) for i, w in wide if llines[i - 1] not in blines]
print("## Widths")
print(f"landed: {len(llines) - 1} lines, maximum width {max(len(l) for l in llines)}; "
      f"lines over 100: {len(wide)} (of which new or changed: {len(new_wide)})")
for i, w in wide:
    print(f"  line {i}: {w} characters ({'NEW' if (i, w) in new_wide else 'verbatim from base'})")
if new_wide:
    fail.append("new lines over 100 characters")
print()
print("## Hygiene")
checks = {
    "LF line ends (no CR)": b"\r" not in land_b,
    "final newline": land.endswith("\n") and not land.endswith("\n\n"),
    "no tab": "\t" not in land,
    "no trailing whitespace": not any(l != l.rstrip() for l in llines),
    "no #-command at column 0": not any(re.match(r"#[a-z]", l) for l in llines),
    "set_option lines as in the base": sorted(l for l in llines if l.startswith("set_option"))
        == sorted(l for l in base.split("\n") if l.startswith("set_option")),
    "no private declaration": not any(re.match(r"(?:\S+\s+)*private\s", l) and
                                      not l.startswith(("--", "/-", " ")) for l in llines),
}
for k, v in checks.items():
    print(f"- {k}: {'yes' if v else '**NO**'}")
    if not v:
        fail.append(k)
print()
if fail:
    print("WIDTHS/HYGIENE: FAIL — " + "; ".join(fail))
    sys.exit(1)
print("WIDTHS/HYGIENE: PASS")
