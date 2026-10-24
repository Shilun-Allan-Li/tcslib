"""Assemble the Q-U1 API probe: copies of Build/StepBlockForward and Build/InputDevice with the
proposed simps attribute inserted after each definition, then a tail (checks, route, controls).
Every edit is asserted. Usage: mk_api_probe.py <worktree> <tail.lean> <out.lean>"""
import sys, re
wt, tail, out = sys.argv[1], sys.argv[2], sys.argv[3]
sbf = open(f"{wt}/TCSlib/Complexity/TuringMachine/Build/StepBlockForward.lean").read()
ind = open(f"{wt}/TCSlib/Complexity/TuringMachine/Build/InputDevice.lean").read()
def split_imports(t):
    lines = t.split("\n")
    imps = [l for l in lines if l.startswith("import ")]
    body = "\n".join(l for l in lines if not l.startswith("import "))
    return imps, body
i1, b1 = split_imports(sbf); i2, b2 = split_imports(ind)
anchor1 = ("  workTapePos := Fin.addCases (motive := fun _ => ℤ) c.workTapePos fun _ => 0\n"
           "  output := c.output\n")
assert b1.count(anchor1) == 1, "anchor1"
ins1 = ("\n/-! The encoding's fields as equations (review probe of the proposed API). -/\n"
        "attribute [simps (config := { isSimp := false }) state inputPos workTapes workTapePos "
        "output]\n  forwardLoopCfg\n")
b1 = b1.replace(anchor1, anchor1 + ins1)
anchor2 = "    Fin.lastCases rp c.workTapePos, c.output⟩\n"
assert b2.count(anchor2) == 1, "anchor2"
ins2 = ("\n/-! The layout's fields as equations (review probe of the proposed API). -/\n"
        "attribute [simps (config := { isSimp := false }) state inputPos workTapes workTapePos "
        "output]\n  rulerHostCfg\n")
b2 = b2.replace(anchor2, anchor2 + ins2)
anchor3 = """theorem pairEncode_pairEncode_drop (u α x : List Bool) :
    (pairEncode u (pairEncode α x)).drop (2 * u.length + 2 * α.length + 4) = x := by
  have hd (v z : List Bool) : (pairEncode v z).drop (2 * v.length + 2) = z := by
    have hl : ((v.flatMap fun b => [b, b]) ++ [false, true]).length = 2 * v.length + 2 := by
      have h := universal_pair_length v []
      simpa [pairEncode] using h
    rw [show pairEncode v z = ((v.flatMap fun b => [b, b]) ++ [false, true]) ++ z from rfl]
    exact List.drop_left' hl
  rw [show 2 * u.length + 2 * α.length + 4 = (2 * u.length + 2) + (2 * α.length + 2) by ring,
    ← List.drop_drop, hd, hd]
"""
assert b2.count(anchor3) == 1, "anchor3"
new3 = """theorem pairEncode_pairEncode_drop (u α x : List Bool) :
    (pairEncode u (pairEncode α x)).drop (2 * u.length + 2 * α.length + 4) = x := by
  rw [show 2 * u.length + 2 * α.length + 4 = (2 * u.length + 2) + (2 * α.length + 2) by ring,
    ← List.drop_drop, pairEncode_drop, pairEncode_drop]
"""
pre3 = """/-- **The payload after the header.** Dropping the header of length `2|u| + 2` from
`pairEncode u x` leaves `x`: the ruler device's `z.drop ℓ = y` for the code-first input.

**Proof sketch.** The pairing is the header `pairEncode u []` followed by `x`, and that header
has length `2|u| + 2` (`Turing.length_pairEncode`). -/
theorem pairEncode_drop (u x : List Bool) : (pairEncode u x).drop (2 * u.length + 2) = x := by
  have split : pairEncode u x = pairEncode u [] ++ x := by
    rw [pairEncode_eq, pairEncode_eq, List.append_nil]
  have width : (pairEncode u []).length = 2 * u.length + 2 := by
    rw [length_pairEncode, List.length_nil, Nat.add_zero]
  rw [split, ← width, List.drop_left]

"""
b2 = b2.replace(anchor3, new3)
anchor5 = "/-- **The payload after the header.** Dropping the header of length `2|u| + 2|α| + 4` from\n"
assert b2.count(anchor5) == 1, "anchor5"
b2 = b2.replace(anchor5, pre3 + anchor5)
anchor4 = """      d.workTapes r (d.workTapePos r + p) = FinTM.bufferTape (List.replicate ℓ true) p
"""
assert b2.count(anchor4) == 1, "anchor4"
ins4 = """
/-- The bounded-prefix ruler presentation, unfolded. -/
theorem rulerAt_iff {K : ℕ} {S : Type*} {y z : List Bool} {ℓ : ℕ} {r : Fin K}
    {d : Cfg K Bool S z} {i : Fin (y.length + 2)} :
    RulerAt ℓ r d i ↔ 0 < ℓ ∧ ℓ ≤ z.length ∧ z.drop ℓ = y ∧ d.inputPos.val = ℓ + i.val ∧
      ∀ p : ℤ, -1 ≤ p → p ≤ (ℓ : ℤ) →
        d.workTapes r (d.workTapePos r + p) = FinTM.bufferTape (List.replicate ℓ true) p :=
  Iff.rfl
"""
b2 = b2.replace(anchor4, anchor4 + ins4)
imps = list(dict.fromkeys(i1 + i2))
assert "import TCSlib.Complexity.TuringMachine.Build.StepBlockForward" not in imps
assert "import TCSlib.Complexity.TuringMachine.Build.InputDevice" not in imps
t = open(tail).read()
open(out, "w").write("\n".join(imps) + "\n" + b1 + "\n" + b2 + "\n" + t)
print("imports:", imps)
