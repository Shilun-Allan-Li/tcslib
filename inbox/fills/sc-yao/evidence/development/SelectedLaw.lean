/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.CoordinateSwap
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SeedCoordinates
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TapeValues

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Fresh selected coordinates in the actual tape distribution

## Main definitions

None.

## Main results

* `acceptProb_fill`: filling the selected key and row nonces preserves the actual tape law.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Theorem 163.7 (fixing all other randomness in the gate hybrid).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedLaw

open BoolCircuit TCSlib.Cryptography

variable {m : ℕ} (C : DAGCircuit m) (S n : ℕ)
  (hA : ∀ i : Fin C.gates.length, (C.gates[i.val]).args.length ≤ 2) (hS : C.size ≤ S)
  (seed : List Bool → GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (hK : ∀ q (w : Fin C.size) b (t : Fin n),
    (seed q).1 w b t = q.getD ((b.toNat * S + w) * n + t) false)
  (hR₀ : ∀ q (i : Fin C.gates.length) (a : Fin (C.gates[i.val]).args.length → Bool)
      (t : Fin n),
    ((seed q).2.1 i a).1 t = q.getD (2 * S * n + (4 * i +
      (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) * (2 * n) + t) false)
  (hR₁ : ∀ q (i : Fin C.gates.length) (a : Fin (C.gates[i.val]).args.length → Bool)
      (t : Fin n),
    ((seed q).2.1 i a).2 t = q.getD (2 * S * n + (4 * i +
      (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) * (2 * n) + n + t) false)
  (hP : ∀ q (i : Fin C.gates.length) (a : Fin (C.gates[i.val]).args.length → Bool)
      (t : Fin (C.gates[i.val]).args.length),
    (seed q).2.2 i a t = xor (a t) (q.getD (10 * S * n + 2 * i + t) false))


include hA hS hK hR₀ hR₁ hP

/-- For a seed with the four actual addressed tape readers, independently replacing one
inactive key and every matched row nonce preserves every sampler's acceptance probability.
All shifts and unused padded coordinates retain their actual distribution; there is no
uniformity assumption on the derived assignment permutations. No occurrence-capacity or
key-value-distinctness premise is required. [PS10, Theorem 163.7]

**Proof sketch.** Split the complete tape into its retained shift/unused-block parameter
and independent actual key/nonce values. Convert the value table and challenge into their
existing coordinate types. The seed's inverse reader identifies the original sample with
these coordinates, and the filled-seed reader identifies replacement with the matched
coordinate exchange. Apply that exchange's proved uniform acceptance law and transport
back through the two coordinate equivalences. -/
theorem acceptProb_fill
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (u : Fin C.size) (q : ℕ)
    (hargs : ∀ i : Fin C.gates.length, C.gates[i.val].args.Nodup)
    (hcomplete : ∀ i a, a ∈ rows i) (hrows : ∀ i, (rows i).Nodup)
    {γ κ : Type*} [Fintype κ]
    (X : GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)) → γ)
    (D : γ → κ → Bool) :
    acceptProb
      (fun z : (Fin (10 * S * n + 2 * S) → Bool) ×
          ((Fin n → Bool) × (Fin (q + 1) → Fin n → Bool)) =>
        X (SelectedSeed.fill C rows (seed (List.ofFn z.1)) u q z.2.1 z.2.2)) D =
      acceptProb (fun r : Fin (10 * S * n + 2 * S) → Bool => seed (List.ofFn r) |> X) D := by
  classical
  let P := TapeValues.Rest C S n hA hS
  let V := Fin n → Bool
  let e := (TapeValues.equiv C S n hA hS).trans (SeedCoordinates.paramEquiv C V P)
  let c := SeedCoordinates.challengeEquiv q V
  let perm : P → SeedCoordinates.Permutations C := TapeValues.permutation C S n hA hS
  let pick := fun p : P => SeedCoordinates.pick C rows (perm p) u q
  let place := fun p : P => SeedCoordinates.place C rows (perm p) u q
  have hmatch : ∀ p i j, pick p i = some j ↔ place p j = some i :=
    fun p => SeedCoordinates.pick_iff_place C rows (perm p) u q hargs hcomplete hrows
  have hSeed (z : P × (SeedCoordinates.Index C → V)) :
      seed (List.ofFn (e.symm z)) =
        (SeedCoordinates.seedEquiv C V).symm (perm z.1, z.2) := by
    rcases z with ⟨p, full⟩
    change seed (List.ofFn ((TapeValues.equiv C S n hA hS).symm
      ((SeedCoordinates.paramEquiv C V P).symm (p, full)))) = _
    rw [SeedCoordinates.paramEquiv_symm,
      TapeValues.seed_on_inverse C S n hA hS seed hK hR₀ hR₁ hP]
    rw [SeedCoordinates.seedEquiv_symm, SeedCoordinates.dataEquiv_symm]
  have hFilled (z : P × (SeedCoordinates.Index C → V))
      (t : SeedCoordinates.ChallengeIndex q → V) :
      SelectedSeed.fill C rows (seed (List.ofFn (e.symm z))) u q
          (c.symm t).1 (c.symm t).2 =
        (SeedCoordinates.seedEquiv C V).symm
          (perm (CoordinateSwap.swap pick place (z, t)).1.1,
            (CoordinateSwap.swap pick place (z, t)).1.2) := by
    apply (SeedCoordinates.seedEquiv C V).injective
    have hs := (congrArg (SeedCoordinates.seedEquiv C V) (hSeed z)).trans
      (Equiv.apply_symm_apply (SeedCoordinates.seedEquiv C V) (perm z.1, z.2))
    rw [SeedCoordinates.seedEquiv_eq_data] at hs
    have hp := congrArg Prod.fst hs
    have hd := congrArg Prod.snd hs
    change (seed (List.ofFn (e.symm z))).2.2 = perm z.1 at hp
    change SeedCoordinates.dataEquiv C V
      ((seed (List.ofFn (e.symm z))).1, (seed (List.ofFn (e.symm z))).2.1) = z.2 at hd
    have hc : SeedCoordinates.challengeEquiv q V ((c.symm t).1, (c.symm t).2) = t :=
      Equiv.apply_symm_apply c t
    rw [Equiv.apply_symm_apply, SeedCoordinates.seedEquiv_fill, hp, hd, hc,
      CoordinateSwap.swap_eq]
    rfl
  sorry

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedLaw
