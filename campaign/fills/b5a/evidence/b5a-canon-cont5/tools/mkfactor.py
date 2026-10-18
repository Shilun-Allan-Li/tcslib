"""Write the canonizer cont5 brief's prescribed factoring edit of `CodeSimulator.lean`.

Usage: python3 -I mkfactor.py <base CodeSimulator.lean> <out>

The user's decision of 2026-10-15 (backlog §B5a (j)): continuation 4's in-file pair, the frozen
strip machine `exists_canonStripTM` reproducing the boundary split of `canonPatchWord` (59%), is
factored in continuation 5. Three content-anchored edits, each asserted to match exactly once:

  1. A new private `canonPatchWord_le` (patching a buffered word by a word at least as long gives
     the longer word's buffer), inserted before the strip machine's docstring.
  2. The strip machine's copy block cites it, at the blank tape (statement byte-identical).
  3. `canonPatchWord` is its equal-width instance (statement byte-identical).

The boundary split is then written once.
"""
import sys

base, out = sys.argv[1:3]
t = open(base, encoding="utf-8").read()


def rep(a, b):
    global t
    c = t.count(a)
    assert c == 1, (a[:80], c)
    t = t.replace(a, b)


STRIP_DOC = "/-- **The polynomial-time strip machine.** One finite binary machine computes `canonStrip`\n"
rep(STRIP_DOC, """/-- Patching a buffered word by a word at least as long, over the longer word's interval, gives
the longer word's buffer.

**Proof sketch.** Split at zero and the patch's length. Inside the interval use the patch
branch; outside it both buffers are blank by the public list lookup bound. -/
private lemma canonPatchWord_le (w v : List Bool) (le : w.length ≤ v.length) :
    (fun z : ℤ => if 0 ≤ z ∧ z < (v.length : ℤ) then FinTM.bufferTape v z
      else FinTM.bufferTape w z) = FinTM.bufferTape v := by
  funext z
  by_cases nonneg : 0 ≤ z
  · by_cases inside : z < (v.length : ℤ)
    · simp [nonneg, inside]
    · simp [nonneg, inside, FinTM.bufferTape,
        List.getElem?_eq_none (show w.length ≤ z.toNat by omega)]
  · simp [nonneg, FinTM.bufferTape]

""" + STRIP_DOC)
rep("""    by_cases zero : j.val = 0
    · simp only [zero, if_true, true_and]
      by_cases nonneg : 0 ≤ z
      · by_cases inside : z < (x.length : ℤ)
        · simp [nonneg, inside]
        · simp [nonneg, inside, FinTM.bufferTape]
      · simp [nonneg, FinTM.bufferTape]
    · simp [zero]
""", """    by_cases zero : j.val = 0
    · simp only [zero, if_true, true_and]
      simpa using congrFun (canonPatchWord_le [] x (Nat.zero_le _)) z
    · simp [zero]
""")
rep("""**Proof sketch.** Split at zero and the common length. Inside the interval use the
replacement branch; outside it both buffers are blank by the public list lookup bound. -/
private lemma canonPatchWord (w v : List Bool) (width : v.length = w.length) :
    (fun z : ℤ => if 0 ≤ z ∧ z < (w.length : ℤ) then FinTM.bufferTape v z
      else FinTM.bufferTape w z) = FinTM.bufferTape v := by
  funext z
  by_cases nonneg : 0 ≤ z
  · by_cases inside : z < (w.length : ℤ)
    · simp [nonneg, inside]
    · have past : w.length ≤ z.toNat := by omega
      simp [nonneg, inside, FinTM.bufferTape,
        List.getElem?_eq_none (show v.length ≤ z.toNat by omega)]
  · simp [nonneg, FinTM.bufferTape]
""", """**Proof sketch.** `canonPatchWord_le` at equal widths. -/
private lemma canonPatchWord (w v : List Bool) (width : v.length = w.length) :
    (fun z : ℤ => if 0 ≤ z ∧ z < (w.length : ℤ) then FinTM.bufferTape v z
      else FinTM.bufferTape w z) = FinTM.bufferTape v := by
  have patched := canonPatchWord_le w v width.ge
  rwa [width] at patched
""")
open(out, "w", encoding="utf-8").write(t)
print(f"factored overlay written: {len(t.splitlines())} lines; 1 private added, 2 proofs re-pointed")
