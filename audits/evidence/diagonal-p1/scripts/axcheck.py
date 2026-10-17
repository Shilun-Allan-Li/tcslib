"""Check `#print axioms` output: every printed declaration depends on the standard axioms only
(`propext`, `Classical.choice`, `Quot.sound`, or a subset), and the count is as expected.
Read-only; standard library only.

Usage: python3 -I axcheck.py <lean output> <expected count>
"""
import re
import sys

STD = {"propext", "Classical.choice", "Quot.sound"}
text = open(sys.argv[1], encoding="utf-8").read()
want = int(sys.argv[2])
entries = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text)
none = re.findall(r"'([^']+)' does not depend on any axioms", text)
bad = [(n, a) for n, a in entries if not {x.strip() for x in a.split(",")} <= STD]
other = [l for l in text.split("\n") if l.strip() and "axioms" not in l and not l.startswith(" ")]
print(f"axiom prints: {len(entries) + len(none)} (expected {want}); outside the standard three: "
      f"{len(bad)}; other diagnostics: {len(other)}")
for n, a in bad:
    print(f"  {n}: [{a}]")
for l in other:
    print(f"  {l}")
ok = len(entries) + len(none) == want and not bad and not other
print("AXIOMS: PASS" if ok else "AXIOMS: FAIL")
sys.exit(0 if ok else 1)
