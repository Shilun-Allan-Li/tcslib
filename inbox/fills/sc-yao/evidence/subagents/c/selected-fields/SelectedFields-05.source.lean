/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SelectedSeed
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.GateHybridMessage

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Fields unaffected by selected inactive-key replacement

The selected fill changes the symbolic key label `(u,true)`. False active
keys, unrelated decoding pairs and the encoded message tail therefore remain
fixed. These are reader-based consequences, with no key-value inequality or
encryption hypothesis. Stage output labels are separated from the selected
argument label by circuit acyclicity and the completed-gate rule.

## Main definitions

None.

## Main results

* `keyAt_of_label_ne`, `keyAt_false`: total key lookup outside the selected label is unchanged.
* Active answers and unrelated output decoding pairs are unchanged by selected fill.
* The message tail is independent of selected fill and the hybrid stage.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Protocol 162.6 and Theorem 163.7 (the gate-by-gate hybrid).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields

open Complexity Turing BoolCircuit TCSlib.Cryptography

section Keys

variable {inputs : ℕ} {K ρ : Type} [Inhabited K]
  (C : DAGCircuit inputs)
  (rows : (i : Fin C.gates.length) → List (Fin (C.gates[i.val]).args.length → Bool))
  (s : GarbleSeed C K (ρ × ρ)) (u : Fin C.size) (q : ℕ) (k : K)
  (rs : Fin (q + 1) → ρ)

/-- Total key lookup is unchanged at every symbolic label other than `(u,true)`,
including the default region outside the circuit. [PS10, Theorem 163.7] -/
theorem keyAt_of_label_ne (w : ℕ) (b : Bool) (h : (w, b) ≠ (u.val, true)) :
    keyAt C (SelectedSeed.fill C rows s u q k rs) w b = keyAt C s w b := by
  rw [SelectedSeed.fill_keyAt, if_neg h]

/-- False active keys are unchanged at every vertex, including default vertices.
This is a symbolic-label fact and does not require distinct key values. -/
theorem keyAt_false (w : ℕ) :
    keyAt C (SelectedSeed.fill C rows s u q k rs) w false = keyAt C s w false := by
  simp only [SelectedSeed.fill_keyAt, Prod.mk.injEq, Bool.false_eq_true, and_false, ite_false]

/-- Both key choices are unchanged at a vertex different from the selected vertex. -/
theorem keyAt_of_ne (w : ℕ) (b : Bool) (hw : w ≠ u.val) :
    keyAt C (SelectedSeed.fill C rows s u q k rs) w b = keyAt C s w b :=
  keyAt_of_label_ne C rows s u q k rs w b (fun h => hw (congrArg Prod.fst h))

/-- An output decoding pair at an unrelated vertex is unchanged, for every
prescribed result bit. No encryption assumption is needed. -/
theorem decodePair_fill (w : ℕ) (b : Bool) (hw : w ≠ u.val) :
    FakeObjects.decodePair C (SelectedSeed.fill C rows s u q k rs) w b =
      FakeObjects.decodePair C s w b := by
  rw [FakeObjects.decodePair_eq, FakeObjects.decodePair_eq,
    keyAt_of_ne C rows s u q k rs w b hw, keyAt_of_ne C rows s u q k rs w (!b) hw]

end Keys

/-- The complete false-key answer vector is unchanged by selected fill for
all starting vertices and counts, including zero key width. -/
theorem activeAnswers_fill {inputs width : ℕ} {ρ : Type} (C : DAGCircuit inputs)
    (rows : (i : Fin C.gates.length) → List (Fin (C.gates[i.val]).args.length → Bool))
    (s : GarbleSeed C (Fin width → Bool) (ρ × ρ)) (u : Fin C.size) (q : ℕ)
    (k : Fin width → Bool) (rs : Fin (q + 1) → ρ) (first count : ℕ) :
    FakeObjects.activeAnswers C (SelectedSeed.fill C rows s u q k rs) first count =
      FakeObjects.activeAnswers C s first count := by
  funext t
  rw [FakeObjects.activeAnswers_eq, FakeObjects.activeAnswers_eq, keyAt_false]

/-- The encoded message tail is independent of the hybrid stage: only the
encoded table head depends on the stage. -/
theorem message_tail_stage_eq {inputs width : ℕ} {ρ : Type}
    (M : MultiEnc (Fin width → Bool) (List Bool) ρ) (C : DAGCircuit inputs)
    (s : GarbleSeed C (Fin width → Bool) ρ) (inA outLen : ℕ)
    (output : Fin outLen → ℕ) (v : ℕ → Bool) (stage stage' : ℕ) :
    pairSndD (GateHybridMessage.message M C s inA outLen output v stage) =
      pairSndD (GateHybridMessage.message M C s inA outLen output v stage') := by
  simp only [GateHybridMessage.message_eq, pairSndD_pairEncode]

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields
