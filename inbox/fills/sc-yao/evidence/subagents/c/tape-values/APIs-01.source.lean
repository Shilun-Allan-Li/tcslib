import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TapeValues

set_option maxHeartbeats 0
set_option maxErrors 0

open BoolCircuit TCSlib.Cryptography.SecureComputation.YaoHybridProof

namespace TapeValuesAPI

local instance (p : Prop) : Decidable p := Classical.propDecidable p

example {m : ℕ} (C : DAGCircuit m) (S n : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i.val]).args.length ≤ 2) (hS : C.size ≤ S) :
    Fintype (TapeValues.Rest C S n hA hS) := inferInstance

example {m : ℕ} (C : DAGCircuit m) (S n : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i.val]).args.length ≤ 2) (hS : C.size ≤ S) :
    Nonempty (TapeValues.Rest C S n hA hS) := inferInstance

example {m : ℕ} (C : DAGCircuit m) (S : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i.val]).args.length ≤ 2) (hS : C.size ≤ S)
    (r : Fin (10 * S * 0 + 2 * S) → Bool) (i : Fin S) (t : Fin 2) :
    (TapeValues.equiv C S 0 hA hS r).1.1 i t =
      (List.ofFn r).getD (2 * i + t) false := by
  simpa only [Nat.mul_zero, Nat.zero_add] using TapeValues.equiv_shift C S 0 hA hS r i t

example {m : ℕ} (C : DAGCircuit m) (S : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i.val]).args.length ≤ 2) (hS : C.size ≤ S)
    (z : TapeValues.Rest C S 0 hA hS ×
      ((Fin C.size → Bool → Fin 0 → Bool) ×
        ((i : Fin C.gates.length) → (Fin (C.gates[i.val]).args.length → Bool) →
          (Fin 0 → Bool) × (Fin 0 → Bool)))) :
    TapeValues.equiv C S 0 hA hS ((TapeValues.equiv C S 0 hA hS).symm z) = z :=
  (TapeValues.equiv C S 0 hA hS).apply_symm_apply z

end TapeValuesAPI
