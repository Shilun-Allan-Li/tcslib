"""Write gate probe sources as .lean.txt evidence; do not elaborate them."""

from __future__ import annotations

import json
import os
from pathlib import Path


SEGMENT_GOALS = r"""
section
variable {k : ℕ} {Γ S : Type} {x : List Γ} (M : Turing.MultiTapeTM k Γ S)
  (F : Set (Option S)) (P : (Fin k → ℤ) → Prop) (a b : Turing.Cfg k Γ S x) (t : ℕ)
example : Turing.Segment M F P a b t ↔
    M.runFrom a t = b ∧ (∀ u < t, (M.runFrom a u).state ∉ F) ∧
      ∀ u ≤ t, P (M.runFrom a u).workTapePos := by
  BODY_IFF
example : Turing.Segment M F P a b t =
    (M.runFrom a t = b ∧ (∀ u < t, (M.runFrom a u).state ∉ F) ∧
      ∀ u ≤ t, P (M.runFrom a u).workTapePos) := by
  BODY_EQ
end
"""

BUFFER_GOALS = r"""
example (w : List Bool) (z : ℤ) : Turing.FinTM.bufferTape w z =
    (if 0 ≤ z then w[z.toNat]? else none) := by
  BODY_EQ
example (w : List Bool) : Turing.FinTM.bufferTape w 0 = w[0]? := by
  BODY_ZERO
"""


def main() -> None:
    records = Path(__file__).resolve().parents[3]
    scratch = Path(os.environ["TCSLIB_SCRATCH"])
    info = json.loads((scratch / "gate-source-exports/summary.json").read_text())
    gate = records / "campaign/gates/106-sg1-dedup/evidence/current"
    (gate / "seal").mkdir(exist_ok=True)
    unsealed = SEGMENT_GOALS.replace("BODY_IFF", "rfl").replace("BODY_EQ", "rfl")
    sealed = SEGMENT_GOALS.replace(
        "BODY_IFF", "fail_if_success rfl\n  exact Turing.segment_iff M F P a b t").replace(
        "BODY_EQ", "fail_if_success rfl\n  exact propext (Turing.segment_iff M F P a b t)")
    controls = ("\n-- Both delta controls close before the seal.\n" + unsealed +
                "\nattribute [local irreducible] Turing.Segment\n" +
                "-- The identical rfl attempts fail after the seal; the public equation closes them.\n" + sealed)
    sg1 = Path(info["106-sg1-dedup"]["head_export"])
    for path in ("ClassNP/Tautology", "TuringMachine/Build/CounterLoop",
                 "TuringMachine/Robustness/SingleTape"):
        source = (sg1 / f"TCSlib/Complexity/{path}.lean").read_text()
        lines = source.splitlines(keepends=True)
        imports = [line for line in lines if line.startswith("import ")]
        assert imports
        anchor = imports[-1]
        assert source.count(anchor) == 1
        source = source.replace(anchor, anchor + controls + "\n")
        (gate / "seal" / (Path(path).name + ".lean.txt")).write_text(source)
    unsealed = BUFFER_GOALS.replace("BODY_EQ", "rfl").replace("BODY_ZERO", "rfl")
    sealed = BUFFER_GOALS.replace(
        "BODY_EQ", "fail_if_success rfl\n  exact Turing.FinTM.bufferTape_eq w z").replace(
        "BODY_ZERO", "fail_if_success rfl\n  exact Turing.FinTM.bufferTape_nat w 0")
    fragment = "import TCSlib.Complexity.SpaceComplexity.Machines.Frag\n\n" + unsealed
    fragment += "\nattribute [local irreducible] Turing.FinTM.bufferTape\n" + sealed
    fragment += r"""

set_option autoImplicit false
open Turing

example (w : List Bool) (k : ℕ) (hkw : k < w.length) :
    FinTM.bufferTape (w.take k ++ w[k] :: w.drop (k + 2))
      (((k + 1 : ℕ) : ℤ) - 1) = some w[k] := by
  have hlen : (w.take k).length = k := List.length_take_of_le (Nat.le_of_lt hkw)
  have hpos : (((k + 1 : ℕ) : ℤ) - 1) = ((w.take k).length : ℤ) := by
    rw [hlen]; push_cast; ring
  rw [hpos, FinTM.bufferTape_nat, List.getElem?_append_right le_rfl, Nat.sub_self]
  rfl
"""
    (gate / "seal/FragCell.lean.txt").write_text(fragment)
    for name in info:
        evidence = records / "campaign/gates" / name / "evidence/current/axioms"
        evidence.mkdir(exist_ok=True)
        census = json.loads((evidence.parent / "freeze/census.json").read_text())
        modules = sorted(path[:-5].replace("/", ".") for path in census)
        names = sorted({n for row in census.values()
                        for n in row["public_added"] + row["public_body_changed"]})
        probe = "\n".join("import " + module for module in modules) + "\n\n"
        probe += "\n".join("#print axioms " + constant for constant in names) + "\n"
        if name.startswith("114"):
            probe += r"""

-- Enumerate every non-private imported constant from the new module, including auxiliaries.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some target := env.getModuleIdx? `TCSlib.Complexity.TuringMachine.NatBits
    | throwError "NatBits is missing from the imported module table"
  let names := env.constants.toList.filterMap fun (n, ci) =>
    if env.getModuleIdxFor? n == some target && !isPrivateName n then some (n, ci) else none
  for (n, ci) in names.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    let kind := match ci with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .inductInfo _ => "inductive"
      | .quotInfo _ => "quotient"
    logInfo m!"PUBLIC_CONSTANT {n} kind={kind} internal={n.isInternalDetail}"
"""
            sanity = r"""import TCSlib.Complexity.TuringMachine.NatBits

set_option autoImplicit false

example : (Nat.bits 0).length = 0 := by rw [Nat.zero_bits]; rfl
example : ¬ (Nat.bits 0).length = Nat.log 2 0 + 1 := by
  rw [Nat.zero_bits, Nat.log_zero_right]; decide
example : (Nat.bits 1).length = Nat.log 2 1 + 1 := by
  rw [Nat.one_bits, Nat.log_one_right]; rfl
example : 2 ^ (Nat.bits 0).length = 2 * 0 + 1 := by rw [Nat.zero_bits]; decide
example : (Nat.bits (1 + 1)).length ≤ 0 + 2 :=
  Complexity.LogProg.length_bits_succ_le (m := 1) (e := 0) (by decide)
example : Nat.ofDigits 2 (([] : List Bool).map Bool.toNat) < 2 ^ ([] : List Bool).length :=
  Complexity.LogProg.ofDigits_lt_two_pow []
example : Nat.ofDigits 2 ([false, true].map Bool.toNat) < 2 ^ ([false, true] : List Bool).length :=
  Complexity.LogProg.ofDigits_lt_two_pow [false, true]
"""
            (evidence.parent / "Sanity.lean.txt").write_text(sanity)
        (evidence / "Axioms.lean.txt").write_text(probe)
    print("Wrote probe sources only; no elaboration was run.")


if __name__ == "__main__":
    main()
