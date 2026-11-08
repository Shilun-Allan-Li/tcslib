/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.Reductions
import TCSlib.Complexity.Randomized.PTMEquiv

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The BP· operator and BP·P = BPP

[AB09, Chapter notes, p. 141]: "The notation `BP · NP` defined in Section 7.6 can be
generalized to arbitrary complexity classes … Under this generalization, `BP · P = BPP`."
We generalize [AB09, Def 7.17] to `BP·𝒞 = {L | L ≤ᵣ C for some C ∈ 𝒞}`.

## Main definitions

* `Randomized.BPdot` — `BP·𝒞`.

## Main results

* `Randomized.RandReducible.of_polyTimeReducible_right` — `A ≤ᵣ B ≤ₚ C ⇒ A ≤ᵣ C`.
* `Randomized.BPdot_NP_eq_BPNP` — the generalization recovers [AB09, Def 7.17].
* `Randomized.BPdot_P_eq_BPP`, `Randomized.BPdot_P_eq_BPP_PTM` — `BP·P = BPP` [AB09, p. 141].
* `Randomized.BPdot_BPP_eq_BPP` — `BP·BPP = BPP`.

## Divergences

* The book defers the generalization to [Koz06, Lecture G], whose `BP·𝒞` asks for `A ∈ 𝒞`
  with `Pr_y[x ∈ L ↔ ⟨x, y⟩ ∈ A] ≥ 3/4`. We keep Def 7.16's reductions and threshold `2/3` and
  let the target range over `𝒞`; for `𝒞 = P` both give `BPP`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
* [Koz06] D. Kozen, *Theory of Computation*, Springer, 2006.
-/

namespace Randomized

open Complexity Turing

/-- **`BP·𝒞`** [AB09, p. 141, generalizing Def 7.17]: the languages randomly reducible to some
language of `𝒞`. -/
def BPdot (𝒞 : Set (Language Bool)) : Set (Language Bool) :=
  {L | ∃ C ∈ 𝒞, L ≤ᵣ C}

/-- Every language reduces randomly to itself. -/
theorem RandReducible.refl (L : Language Bool) : L ≤ᵣ L :=
  RandReducible.of_polyTimeReducible ⟨id, polyTimeComputable_id, fun _ => Iff.rfl⟩

/-- `𝒞 ⊆ BP·𝒞`. -/
theorem subset_BPdot (𝒞 : Set (Language Bool)) : 𝒞 ⊆ BPdot 𝒞 :=
  fun L hL => ⟨L, hL, RandReducible.refl L⟩

/-- `BP·` is monotone. -/
theorem BPdot_mono {𝒞 𝒟 : Set (Language Bool)} (h : 𝒞 ⊆ 𝒟) : BPdot 𝒞 ⊆ BPdot 𝒟 :=
  fun _ ⟨C, hC, hred⟩ => ⟨C, h hC, hred⟩

/-- A randomized reduction followed by a Karp reduction: `A ≤ᵣ B ≤ₚ C ⇒ A ≤ᵣ C`. -/
theorem RandReducible.of_polyTimeReducible_right {A B C : Language Bool} (h₁ : A ≤ᵣ B)
    (h₂ : B ≤ₚ C) : A ≤ᵣ C := by
  classical
  obtain ⟨f, a, k, hf, hprob⟩ := h₁
  obtain ⟨g, hg, hgB⟩ := h₂
  refine ⟨g ∘ f, a, k, hg.comp hf, fun x => (hprob x).trans (le_of_eq ?_)⟩
  exact randProb_congr fun r => by simp only [Function.comp, ← hgB]

/-- **`BP·NP = {L | L ≤ᵣ 3SAT}`** [AB09, Def 7.17], as `3SAT` is `NP`-complete. -/
theorem BPdot_NP_eq_BPNP : BPdot NP = BPNP :=
  Set.Subset.antisymm
    (fun _ ⟨_, hC, hred⟩ => hred.of_polyTimeReducible_right (SAT3_NPHard _ hC))
    (fun _ hL => ⟨SAT3, SAT3_mem_NP, hL⟩)

/-- **`BP·P = BPP`** [AB09, p. 141], certificate form.

**Proof sketch.** `⊆`: `P ⊆ BPP` and `BPP` is closed under randomized reductions
(`InBPP.of_randReducible`). `⊇`: if `M` is a polynomial-time verifier for `L`, its accepting
set `V₁ = {⟨x, r⟩ | M(x, r) = 1}` is in `P`, and the reduction `⟨x, r⟩ ↦ ⟨x, r⟩` lands in `V₁`
exactly when `M(x, r) = 1`, which agrees with `L(x)` with probability `≥ 2/3`. -/
theorem BPdot_P_eq_BPP : BPdot P = {L | InBPP polyTimeModel L} := by
  classical
  refine Set.Subset.antisymm
    (fun _ ⟨_, hC, hred⟩ => InBPP.of_randReducible hred (inBPP_polyTimeModel_of_mem_P hC)) ?_
  rintro L ⟨M, a, k, ⟨V₁, V₀, hV₁, -, hMV⟩, hL⟩
  have hiff : ∀ x r, M x r = true ↔ Turing.pairEncode x r ∈ V₁ := fun x r => by
    simpa only [boolVerifier, Option.some.injEq] using (hMV x r).1
  refine ⟨V₁, hV₁, id, a, k, polyTimeComputable_id, fun x => ?_⟩
  by_cases hx : x ∈ L
  · refine ((hL x).1 hx).trans (randProb_mono fun r hr => ?_)
    simpa [hx, ← hiff] using hr
  · refine ((hL x).2 hx).trans (randProb_mono fun r hr => ?_)
    simpa [hx, ← hiff] using hr

/-- **`BP·BPP = BPP`**: `BPP` is closed under randomized reductions. [AB09, §7.6] -/
theorem BPdot_BPP_eq_BPP :
    BPdot {L | InBPP polyTimeModel L} = {L | InBPP polyTimeModel L} :=
  Set.Subset.antisymm (fun _ ⟨_, hC, hred⟩ => InBPP.of_randReducible hred hC) (subset_BPdot _)

/-- **`BP·P = BPP`** [AB09, p. 141], PTM form. -/
theorem BPdot_P_eq_BPP_PTM : BPdot P = BPP_PTM := by
  rw [BPdot_P_eq_BPP, BPP_PTM_eq]

end Randomized
