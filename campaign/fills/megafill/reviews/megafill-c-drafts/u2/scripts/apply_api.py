"""Apply the proposed Q-U1 API (and the optional extras) to copies of the two modules, asserted.
Usage: apply_api.py <TuringMachine dir> [--extras]"""
import sys
d = sys.argv[1]; extras = "--extras" in sys.argv
p1 = f"{d}/Build/StepBlockForward.lean"; t = open(p1).read()
a = ("  workTapePos := Fin.addCases (motive := fun _ => ℤ) c.workTapePos fun _ => 0\n"
     "  output := c.output\n")
assert t.count(a) == 1
t = t.replace(a, a + "\n/-! The encoding's fields as equations, without the `simp` attribute. -/\n"
              "attribute [simps (config := { isSimp := false }) state inputPos workTapes workTapePos "
              "output]\n  forwardLoopCfg\n")
open(p1, "w").write(t)
p2 = f"{d}/Build/InputDevice.lean"; t = open(p2).read()
a = "    Fin.lastCases rp c.workTapePos, c.output⟩\n"
assert t.count(a) == 1
t = t.replace(a, a + "\n/-! The layout's fields as equations, without the `simp` attribute. -/\n"
              "attribute [simps (config := { isSimp := false }) state inputPos workTapes workTapePos "
              "output]\n  rulerHostCfg\n")
if extras:
    a = "      d.workTapes r (d.workTapePos r + p) = FinTM.bufferTape (List.replicate ℓ true) p\n"
    assert t.count(a) == 1
    t = t.replace(a, a + "\n/-- The bounded-prefix ruler presentation, unfolded. -/\n"
        "theorem rulerAt_iff {K : ℕ} {S : Type*} {y z : List Bool} {ℓ : ℕ} {r : Fin K}\n"
        "    {d : Cfg K Bool S z} {i : Fin (y.length + 2)} :\n"
        "    RulerAt ℓ r d i ↔ 0 < ℓ ∧ ℓ ≤ z.length ∧ z.drop ℓ = y ∧ d.inputPos.val = ℓ + i.val ∧\n"
        "      ∀ p : ℤ, -1 ≤ p → p ≤ (ℓ : ℤ) →\n"
        "        d.workTapes r (d.workTapePos r + p) = FinTM.bufferTape (List.replicate ℓ true) p :=\n"
        "  Iff.rfl\n")
open(p2, "w").write(t)
print("applied", "with extras" if extras else "")
