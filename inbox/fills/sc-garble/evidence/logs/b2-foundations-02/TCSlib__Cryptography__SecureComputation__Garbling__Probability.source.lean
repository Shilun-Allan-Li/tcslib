/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.HardcoreBit.Basic
import TCSlib.Cryptography.OneWayFunctions.Basic
import Mathlib.Data.Fintype.Pi

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Independent marginals and first successful openings

## Main definitions

This module adds no definitions.

## Main results

* `SecureComputation.GarblingProbability.findSome_eq_some_of_dichotomy`: a successful
  entry and no other successful value determine the first successful opening.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.3, Claim 159.a.
-/

namespace TCSlib.Cryptography.SecureComputation.GarblingProbability

open TCSlib.Cryptography

/-- If a list contains an entry mapped to `some b`, and every entry maps to either
`none` or `some b`, its first successful image is `some b`:
`(∃ a ∈ l, f a = some b) → (∀ a ∈ l, f a = none ∨ f a = some b) →
  l.findSome? f = some b`. -/
theorem findSome_eq_some_of_dichotomy {α β : Type} (l : List α) (f : α → Option β) (b : β)
    (hex : ∃ a ∈ l, f a = some b)
    (hall : ∀ a ∈ l, f a = none ∨ f a = some b) : l.findSome? f = some b := by
  cases hfind : l.findSome? f with
  | none =>
    obtain ⟨a, ha, hfa⟩ := hex
    have hn := List.findSome?_eq_none_iff.mp hfind a ha
    cases hn.symm.trans hfa
  | some c =>
    obtain ⟨a, ha, hfa⟩ := List.exists_of_findSome?_eq_some hfind
    rcases hall a ha with hn | hb
    · cases hn.symm.trans hfa
    · exact hfa.symm.trans hb

/-- Distinct argument vertices and a different output vertex give an independent output
key and argument-key table:
`ks ↦ (ks out b, fun j => ks (arg j))` pushes uniform to uniform, if `arg` is injective
and `arg j ≠ out` for every `j`.

**Proof sketch.** Restrict the uniform vertex table to the injection from `J ⊕ Unit`
which selects argument vertices on the left and the output vertex on the right. Split
that restricted table along the sum, evaluate the unit coordinate and output bit, and
swap the two resulting independent factors. -/
theorem pushesUniform_output_argKeys {I J K : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype K] [Nonempty K]
    (arg : J → I) (hinj : Function.Injective arg) (out : I)
    (hne : ∀ j, arg j ≠ out) (b : Bool) :
    HardcoreBit.PushesUniform (fun ks : I → Bool → K =>
      (ks out b, fun j => ks (arg j))) := by
  let select : J ⊕ Unit → I := Sum.elim arg (fun _ => out)
  have hselect : Function.Injective select := by
    intro x y hxy
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (hinj hxy)
      | inr y => exact (hne x hxy).elim
    | inr x =>
      cases y with
      | inl y => exact (hne y hxy.symm).elim
      | inr y => exact congrArg Sum.inr (Subsingleton.elim x y)
  -- Restrict, then split the argument and output coordinates.
  have hrestrict := HardcoreBit.pushesUniform_restrict (O := Bool → K) hselect
  have hsplit := hrestrict.comp (HardcoreBit.pushesUniform_equiv
    (Equiv.sumArrowEquivProdArrow J Unit (Bool → K)))
  have hout := (HardcoreBit.pushesUniform_eval (γ := Bool → K) ()).comp
    (HardcoreBit.pushesUniform_eval (γ := K) b)
  -- Evaluate only the output coordinate; retain the full argument-key table.
  exact (hsplit.comp (HardcoreBit.pushesUniform_id.prodMap hout)).comp
    (HardcoreBit.pushesUniform_equiv (Equiv.prodComm (J → Bool → K) K))

/-- Reading one row of a uniform dependent family of coin tables is uniform:
`r ↦ r i a : ((i : I) → A i → ρ) → ρ` pushes uniform to uniform. -/
theorem pushesUniform_rowCoin {I : Type} [Fintype I] [DecidableEq I] {A : I → Type}
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] {ρ : Type} [Fintype ρ] (i : I) (a : A i) :
    HardcoreBit.PushesUniform (fun r : (i : I) → A i → ρ => r i a) := by
  classical
  exact (HardcoreBit.pushesUniform_equiv (Equiv.piCurry (fun i (_ : A i) => ρ)).symm).comp
    (HardcoreBit.pushesUniform_eval (γ := ρ) ⟨i, a⟩)

/-- Independent uniform keys and a uniform row-coin map give their joint marginal:
`(ks,r) ↦ (ks out b,(fun j => ks (arg j),coin r))` pushes uniform to uniform,
if argument vertices are distinct and exclude `out`, and `coin` pushes uniform to uniform. -/
theorem pushesUniform_output_argKeys_row {I J K R ρ : Type}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype K] [Nonempty K] [Fintype R] [Fintype ρ]
    (arg : J → I) (hinj : Function.Injective arg) (out : I)
    (hne : ∀ j, arg j ≠ out) (b : Bool) (coin : R → ρ)
    (hcoin : HardcoreBit.PushesUniform coin) :
    HardcoreBit.PushesUniform (fun t : (I → Bool → K) × R =>
      (t.1 out b, (fun j => t.1 (arg j), coin t.2))) := by
  exact ((pushesUniform_output_argKeys arg hinj out hne b).prodMap hcoin).comp
    (HardcoreBit.pushesUniform_equiv (Equiv.prodAssoc K (J → Bool → K) ρ))

end TCSlib.Cryptography.SecureComputation.GarblingProbability
