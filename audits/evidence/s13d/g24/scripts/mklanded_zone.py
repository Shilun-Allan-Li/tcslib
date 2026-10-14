"""Write the landed form of Build/Zone.lean (read-only on the checkout and the unit).

Usage: python3 -I mklanded_zone.py <worktree> <part-Z body> <out.lean> <imports-file> <doc-file>

Every edit is a content-anchored replacement asserted to match exactly once:
  1. the imports are replaced by the lines of <imports-file>;
  2. the module docstring is replaced by <doc-file>;
  3. five blocks are deleted (each from a unique start anchor to a unique end anchor, the end
     anchor kept), and the deleted text is checked to declare exactly the expected names;
  4. the private `zoneCascadeRight_frame` becomes public with the unit's docstring;
  5. two retained docstrings lose their references to the retired binary realization, and the
     sketch of the private `zoneSide_adjacent` gets its `**Proof sketch.**` label;
  6. the Part Z body is appended inside the namespace, minus its sorried copy of
     `zoneCascadeRight_frame`.
The deleted blocks are written next to <out.lean> as <out>.deleted.txt.
"""
import re
import sys

wt, zbody, out, impf, docf = sys.argv[1:6]
src = open(f"{wt}/TCSlib/Complexity/TuringMachine/Build/Zone.lean", encoding="utf-8").read()
body = open(zbody, encoding="utf-8").read()
imports = open(impf, encoding="utf-8").read()
doc = open(docf, encoding="utf-8").read()


def one(s, a):
    n = s.count(a)
    assert n == 1, f"anchor occurs {n} times: {a[:70]!r}"
    return s.index(a)


# 1. imports
old_imp = ("import TCSlib.Complexity.TuringMachine.Simulation\n"
           "import TCSlib.Complexity.TuringMachine.Build.Embed\n"
           "import TCSlib.Complexity.TuringMachine.Build.Seam\n"
           "import TCSlib.Complexity.TuringMachine.Build.Catalog\n")
one(src, old_imp)
src = src.replace(old_imp, imports)
# 2. module docstring
ds = one(src, "/-!\n# Machine-construction library: the zoned tape carrier (Z2)")
de = one(src, "-/\n\nnamespace Turing\n") + len("-/\n")
src = src[:ds] + doc.rstrip("\n") + "\n" + src[de:]
# 3. deletions
DECL = re.compile(r"^(?:private\s+)?(?:theorem|def|lemma)\s+(\S+)", re.M)
cuts = [
    ("/-! ### The paired-cell codec (decision 13.2) -/\n", "/-! ### Layout arithmetic -/\n",
     ["zoneCellBits", "zoneCellOf", "zoneCellOf_bits"]),
    ("/-- The physical realization of zone contents: home at cells `0`/`1`,\n",
     "/-- The empty contents (blank home, every zone empty). -/\n", ["zoneTape"]),
    ("/-- The empty contents realize the almost-blank tape: the home pair\n",
     "/-! ### The represented word -/\n", ["zoneTape_empty", "zoneTape_blank_outside"]),
    ("/-- Writing the home changes exactly the two home cells of the physical\n",
     "/-- The virtual head steps right: the home is pushed onto the inner end of\n",
     ["zoneTape_homeWrite"]),
    ("/-! ### The machine rows -/\n", "end Turing\n",
     ["zoneStageWord", "zoneStageWord_length", "zoneStageWord_getElem", "zoneStageSlot",
      "zoneStage_rightWindow", "zoneStage_leftWindow", "zoneStage_window_bounds",
      "exists_zoneShiftInTM", "exists_zoneShiftOutTM"]),
]
deleted = []
for a, b, names in cuts:
    i = one(src, a)
    j = one(src, b)
    assert i < j
    blk = src[i:j]
    got = DECL.findall(blk)
    assert got == names, (got, names)
    deleted.append(blk)
    src = src[:i] + src[j:]
# 4. promotion
old = ("/-- The recursive descent and ascent only touch levels at or below their\n"
       "index. Induction peels off the outer pair; the base move touches zero. -/\n"
       "private theorem zoneCascadeRight_frame")
m = re.search(r"/-- \*\*The cascade keeps every level above its index\*\*.*?-/\n", body, re.S)
assert m and body.count("**The cascade keeps every level above its index**") == 1
newdoc = m.group(0).replace(
    "(a promotion: the private\n`zoneCascadeRight_frame` of `Build/Zone.lean`, made public at landing with its existing proof;\n"
    "in this unit its statement is sorried)", "(made public at the\n§13d G3/G4 landing, its proof unchanged)")
assert newdoc != m.group(0)
one(src, old)
src = src.replace(old, newdoc + "theorem zoneCascadeRight_frame")
# 5. stale docstrings, and the one pre-existing sketch without its label
for a, b in [
    ("the represented side. Induct on the number of levels, peeling off the\n"
     "unchanged first word until the changed pair is at the front. -/",
     "the represented side.\n\n**Proof sketch.** Induct on the number of levels, peeling off the\n"
     "unchanged first word until the changed pair is at the front. -/"),
    ("slot is beyond the stored words (an unoccupied slot, physically blank —\n"
     "distinct, through the pairing, from an occupied slot storing a blank). -/",
     "slot is beyond the stored words (an unoccupied slot, `⊠` on the zoned tape of\n"
     "`Build/ZoneTape` — distinct from an occupied slot storing a virtual blank). -/"),
    ("Hennie-Stearns amortization consumes (two shift pairs per level, each\n"
     "within the row budget `2^i + i + 1`).",
     "Hennie-Stearns amortization consumes (two shift pairs per level, each\n"
     "within a per-level budget `2^i + i + 1`; the G4 rows of `Build/ZoneRebalance` state their\n"
     "total as `C · (2^{i₀} + 1)`)."),
]:
    one(src, a)
    src = src.replace(a, b)
# 6. append Part Z, minus its sorried frame copy
fs = one(body, m.group(0))
fe = one(body, "  sorry\n\n/-- **The rebalance keeps every level above its scanned index**")
body2 = body[:fs] + body[fe + len("  sorry\n\n"):]
assert "zoneCascadeRight_frame {ℓ" not in body2
tail = "\nend Turing\n"
assert src.endswith(tail)
assert body2.startswith("namespace Turing\n") and body2.rstrip().endswith("end Turing")
inner = body2[len("namespace Turing\n"):].rstrip()
inner = inner[: -len("end Turing")].rstrip() + "\n"
src = src[: -len(tail)] + "\n" + inner + tail
open(out, "w", encoding="utf-8").write(src)
open(out + ".deleted.txt", "w", encoding="utf-8").write("\n".join(deleted))
print(f"landed Zone.lean: {len(src.splitlines())} lines; deleted {sum(len(b.splitlines()) for b in deleted)} lines in {len(deleted)} blocks")
