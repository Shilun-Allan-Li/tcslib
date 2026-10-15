"""Build the probe files from the current unit and patched files (read-only on the worktree).

Usage: python3 -I probes.py <outdir> <worktree>
Writes <outdir>/probes/Sanity.lean (the unit plus the sanity tail), the negative controls
<outdir>/work/neg<N>.lean (each a deliberately false copy of one probe), and
<outdir>/probes/GatedFormProbe.lean: the patched `Hierarchy.lean` in its patched import closure
(the cut check file) plus the gated statement of `space_universal`, extracted verbatim from the
worktree's `Hierarchy.lean` and renamed, proved from the strengthened theorem; and
<outdir>/probes/StepClockDraftFormProbe.lean: the unit plus the draft's statement of
`exists_stepClockTMVia`, extracted verbatim and renamed, proved from the landing form's.
"""
import os, sys
O, WT = sys.argv[1], sys.argv[2]
def rd(p): return open(p, encoding="utf-8").read()
def wr(p, s):
    os.makedirs(os.path.dirname(p), exist_ok=True); open(p, "w", encoding="utf-8").write(s)
unit = rd(os.path.join(O, "B6Hosts.lean"))
san = unit + rd(os.path.join(O, "scripts", "sanity_tail.lean"))
wr(os.path.join(O, "probes", "Sanity.lean"), san)
negs = [
    ("neg1", "example : summaryTag 1 (some true) = 2 := by decide",
     "example : summaryTag 1 (some true) = 1 := by decide"),
    ("neg2", "example : inputCell ([true] : List Bool) (2 - 1) ≠ none := by decide",
     "example : inputCell ([true] : List Bool) (2 - 1) = none := by decide"),
    ("neg3", "example : outSummaryCode (outSummary [true, true]) = 2 := by decide",
     "example : outSummaryCode (outSummary [true, true]) = 1 := by decide"),
    ("neg4", "example : (windowRun emitHalt 0 summaryTag 1 (emitHalt.initCfg []) 0).1 = .exhausted ∧",
     "example : (windowRun emitHalt 0 summaryTag 1 (emitHalt.initCfg []) 0).1 = .halted ∧"),
]
for name, a, b in negs:
    assert san.count(a) == 1, name
    wr(os.path.join(O, "work", name + ".lean"), san.replace(a, b))
# the gated statement, verbatim from the worktree
h = rd(os.path.join(WT, "TCSlib/Complexity/SpaceComplexity/Hierarchy.lean"))
i = h.index("theorem space_universal :")
j = h.index(":= by", i)
stmt = h[i:j].replace("theorem space_universal :", "theorem space_universal_gated_form :", 1)
assert "C * (s + logSpace x.length + 1)" in stmt and stmt.count("space_universal") == 1
check = rd(os.path.join(O, "work", "cut", "Hierarchy.patched.check.lean"))
tail = """
/-! Probe (evidence only): the gated statement follows from the strengthened one. -/

namespace Complexity

open Turing

/-- **The strengthened `space_universal` implies the gated one** with the same machine and
constant: `C · s ≤ C · (s + logSpace |x| + 1)`. The statement is the gated `space_universal`
of the worktree, extracted verbatim and renamed. -/
""" + stmt + """:= by
  obtain ⟨SU, hSU⟩ := space_universal
  refine ⟨SU, fun α => ?_⟩
  obtain ⟨C, hC, h⟩ := hSU α
  refine ⟨C, hC, fun s x output t h₁ h₂ => ?_⟩
  obtain ⟨t', h₃, h₄⟩ := h s x output t h₁ h₂
  exact ⟨t', h₃, h₄.trans (Nat.mul_le_mul_left C (by omega))⟩

end Complexity
"""
wr(os.path.join(O, "probes", "GatedFormProbe.lean"), check.rstrip("\n") + "\n" + tail)
# the draft's statement of the step clock, verbatim, derived from the landing form's
d = rd(os.path.join(WT, "audits/evidence/b6hosts/B6HostsDraft.lean.txt"))
i = d.index("theorem exists_stepClockTMVia ")
j = d.index(":= by", i)
dstmt = d[i:j].replace("theorem exists_stepClockTMVia ", "theorem exists_stepClockTMVia_draft_form ", 1)
assert dstmt.count("exists_stepClockTMVia") == 1 and "Finset.Icc (cp - 1)" in dstmt
assert unit.count("theorem exists_stepClockTMVia ") == 1
sc = unit + """
/-! Probe (evidence only): the landing form's step clock implies the draft's statement, which the
C1 pack cites. The statement below is the draft's, extracted verbatim and renamed. -/

namespace Turing

""" + dstmt + """:= by
  obtain ⟨Q, hQ, dQ, H, inj, finish, timeout, h1, h2, h3, h4, h⟩ :=
    exists_stepClockTMVia e M stopAt
  refine ⟨Q, hQ, dQ, H, inj, finish, timeout, h1, h2, h3, h4, ?_⟩
  intro x c q hq w ct cp hw
  obtain ⟨hf, ht⟩ := h c q hq w ct cp hw
  refine ⟨fun τ hτ hs hm => ?_, fun hn => ?_⟩
  · obtain ⟨T, hT, w', hw', hr, hc, hfr⟩ := hf τ hτ hs hm
    refine ⟨T, hT, w', hw', hr, hc, fun u hu => ?_⟩
    obtain ⟨v, hv, hj, -, -, hcp⟩ := hfr u hu
    exact ⟨v, hv, fun j => (hj j).2, hcp⟩
  · obtain ⟨T, hT, w', hw', hr, hc, hfr⟩ := ht hn
    refine ⟨T, hT, w', hw', hr, hc, fun u hu => ?_⟩
    obtain ⟨v, hv, hj, -, -, hcp⟩ := hfr u hu
    exact ⟨v, hv, fun j => (hj j).2, hcp⟩

end Turing
"""
wr(os.path.join(O, "probes", "StepClockDraftFormProbe.lean"), sc)
print("probes, negative controls, the gated-form and the step-clock draft-form probes rebuilt;",
      "gated statement extracted:", len(stmt.splitlines()), "lines")
