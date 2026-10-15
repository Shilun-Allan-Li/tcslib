"""Sorry-source isolation probe builder (read-only on the sources; standard library only).

Usage: python3 -I isolate.py <tip source tree> <unit-or-probe.lean> <out.lean>

Copies the given file, adds, right after `namespace Turing` of the unit, two axioms whose
statements are the tip's statements of `Turing.ndWriterTM_run_block`
(`Build/NDHost.lean`) and `Turing.exists_ndInterpreterCore` (`NDCodeSimulator.lean`), copied
verbatim, and replaces every use of the two sorried contracts by the axioms. `#print axioms` on
the result then names the sorried contracts each theorem depends on, instead of `sorryAx`.
Each replacement is asserted. Evidence only.
"""
import os
import re
import sys

wt, src, out = sys.argv[1], sys.argv[2], sys.argv[3]


def statement(path, name):
    text = open(os.path.join(wt, path), encoding="utf-8").read()
    i = text.index(f"theorem {name} ")
    j = text.index(":= by", i)
    return text[i:j].rstrip()


wr = statement("TCSlib/Complexity/TuringMachine/Build/NDHost.lean", "ndWriterTM_run_block")
rc = statement("TCSlib/Complexity/TuringMachine/NDCodeSimulator.lean", "exists_ndInterpreterCore")
wr_ax = wr.replace("theorem ndWriterTM_run_block ", "axiom isoWriterBlock ", 1)
rc_ax = rc.replace("theorem exists_ndInterpreterCore ", "axiom isoInterpreterCore ", 1)
body = open(src, encoding="utf-8").read()
uses_wr = len(re.findall(r"\bndWriterTM_run_block j\b", body))
uses_rc = len(re.findall(r"\bexists_ndInterpreterCore c\b", body))
print(f"uses: ndWriterTM_run_block {uses_wr}, exists_ndInterpreterCore {uses_rc}")
assert uses_wr == 1
body = re.sub(r"\bndWriterTM_run_block j\b", "isoWriterBlock j", body)
body = re.sub(r"\bexists_ndInterpreterCore c\b", "isoInterpreterCore c", body)
anchor = "\nnamespace Turing\n"
assert body.count(anchor) >= 1
k = body.index(anchor) + len(anchor)
extra = ("\n/-- Isolation copy of `Turing.ndWriterTM_run_block` (evidence only). -/\n" + wr_ax + "\n")
if uses_rc:
    extra += ("\n/-- Isolation copy of `Turing.exists_ndInterpreterCore` (evidence only). -/\n"
              + rc_ax + "\n")
body = body[:k] + extra + body[k:]
names = re.findall(r"^theorem\s+(\S+)", body, re.M)
body += "\n" + "".join(f"#print axioms Turing.{n}\n" for n in names)
open(out, "w", encoding="utf-8").write(body)
print("theorems printed:", len(names))
