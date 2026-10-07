/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassNP.NP

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The class coNP

[AB09, §2.6.1]: `coNP` is the class of complements of `NP` languages
(Definition 2.19), equivalently the class of languages whose membership is
certified by *every* polynomial-length certificate (Definition 2.20); the
equivalence is [AB09, Exercise 2.24]. This module also records the closure of
`P` under complement that the equivalence rides on, and the two standard
containment facts `P ⊆ NP ∩ coNP` and `P = NP → NP = coNP`.

## Design

* The complement-form Definition 2.19 is primary (it is one line); the
  ∀-certificate form is the characterization theorem, matching [AB09]'s own
  pedagogical ordering in reverse.
* `Complexity.compl_mem_P` is a statement *about the Chapter-1 class `P`* that
  Chapter 1 never needed; it is a new addition beyond the audited Chapter-1
  surface, placed here (its first consumer) and flagged for the phase-1 audit.

## Main definitions

* `Complexity.coNP` — the class coNP. [AB09, Definition 2.19]

## Main results

* `Complexity.compl_mem_P` — `P` is closed under complement.
* `Complexity.mem_coNP_iff_forall` — the ∀-certificate characterization
  [AB09, Definition 2.20 and Exercise 2.24].
* `Complexity.P_subset_NP_inter_coNP` — [AB09, Exercise 2.23].
* `Complexity.NP_eq_coNP_of_P_eq_NP` — [AB09, Exercise 2.25].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.6.1, Definitions 2.19-2.20, pp. 55-56;
  Exercises 2.23-2.25.)
-/

namespace Complexity

/-- **The class coNP** [AB09, Definition 2.19]: the complements of `NP` languages. -/
def coNP : Set (Language Bool) :=
  {L | Lᶜ ∈ NP}

/-- **`P` is closed under complement**: if `L` is decidable in polynomial time then
so is its complement.

**Proof sketch.** Obtain a decider of `L` from `Complexity.mem_P_iff`, read it
pointwise as computing the total singleton-indicator function (the decider's
output is exactly `[indicator L x]`), and postcompose with the Boolean-negation
postprocessor `Turing.FinTM.computesFunInTime_ifEq [true] [false] [true]`
(`w ↦ if w = [true] then [false] else [true]`) via the **timed** total
composition `Turing.FinTM.computesFunInTime_comp` — the untimed
`exists_comp_partial` carries no time bound (phase-1 audit, finding 4). The
composite computes the complement's indicator within a budget polynomial by the
composition ledger and the monotonicity of the explicit polynomial; return
through `Complexity.mem_P_of_dtime_le`. Buffered composition keeps the
intermediate bit off the real output. This is a new statement about the
Chapter-1 class, flagged for audit (plan §6) and certified by the phase-1
round (finding 10). -/
theorem compl_mem_P {L : Language Bool} (h : L ∈ P) : Lᶜ ∈ P := by
  classical
  obtain ⟨C, d, M, hM⟩ := mem_P_iff.mp h
  obtain ⟨N, a, hN⟩ := Turing.FinTM.computesFunInTime_ifEq [true] [false] [true]
  have hfun : M.ComputesFunInTime (fun x => [Turing.MultiTapeTM.indicator L x])
      (fun n => C * (n + 1) ^ d) := fun x => hM x
  -- Buffer the decider's singleton output and apply the timed Boolean postprocessor.
  obtain ⟨M', b, hcomp⟩ := Turing.FinTM.computesFunInTime_comp
    hfun hN
    (fun _ _ hle => Nat.mul_le_mul_left a (Nat.add_le_add_right hle 1))
  have hdec : M'.DecidesInTime Lᶜ
      (fun n => b * (C * (n + 1) ^ d + a * (C * (n + 1) ^ d + 1) + 1)) := by
    intro x
    by_cases hx : x ∈ L
    · have hxc : x ∉ (Lᶜ : Language Bool) := fun hnot => hnot hx
      simpa [Function.comp_apply, Turing.MultiTapeTM.indicator, hx, hxc] using hcomp x
    · have hxc : x ∈ (Lᶜ : Language Bool) := hx
      simpa [Function.comp_apply, Turing.MultiTapeTM.indicator, hx, hxc] using hcomp x
  -- Absorb the linear postprocessor and composition overhead into the same degree.
  refine mem_P_of_dtime_le
    (T := fun n => b * (C * (n + 1) ^ d + a * (C * (n + 1) ^ d + 1) + 1))
    ⟨1, M', by simpa only [one_mul] using hdec⟩
    (b * (C + a * (C + 1) + 1) * 2 ^ d) d ?_
  intro n
  have hpow : 1 ≤ (n + 1) ^ d := Nat.pow_pos (Nat.succ_pos n)
  have hsum : C * (n + 1) ^ d + 1 ≤ (C + 1) * (n + 1) ^ d := by
    calc C * (n + 1) ^ d + 1 ≤ C * (n + 1) ^ d + (n + 1) ^ d :=
        Nat.add_le_add_left hpow _
      _ = (C + 1) * (n + 1) ^ d := by ring
  calc b * (C * (n + 1) ^ d + a * (C * (n + 1) ^ d + 1) + 1)
      ≤ b * (C * (n + 1) ^ d + a * ((C + 1) * (n + 1) ^ d) + (n + 1) ^ d) :=
        Nat.mul_le_mul_left b
          (Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left a hsum) _) hpow)
    _ = b * (C + a * (C + 1) + 1) * (n + 1) ^ d := by ring
    _ ≤ b * (C + a * (C + 1) + 1) * (2 ^ d * (n ^ d + 1)) :=
        Nat.mul_le_mul_left _ (succ_pow_le n d)
    _ = b * (C + a * (C + 1) + 1) * 2 ^ d * (n ^ d + 1) := by ring

/-- **The ∀-certificate characterization of coNP** [AB09, Definition 2.20,
equivalence per Exercise 2.24]: `L ∈ coNP` iff there are a certificate
coefficient `C`, degree `c`, and a verifier `V ∈ P` with
`x ∈ L ↔ ∀ u, |u| = C(|x|+1)^c → x ++ u ∈ V` — the same explicit length
formula as `Complexity.NP` (phase-1 audit repair, finding 1).

**Proof sketch.** Negate the exact-length existential in `NP`'s membership
equivalence for `Lᶜ`: `x ∈ L ↔ ¬(∃ u, |u| = C(|x|+1)^c ∧ x ++ u ∈ V₀)
↔ ∀ u, |u| = C(|x|+1)^c → x ++ u ∈ V₀ᶜ`, and `V₀ᶜ ∈ P` by
`Complexity.compl_mem_P`; both directions instantiate the same `C, c`,
complementing the verifier. Purely logical — no certificate-length computation
is needed (audit finding table). -/
theorem mem_coNP_iff_forall {L : Language Bool} :
    L ∈ coNP ↔ ∃ (C c : ℕ) (V : Language Bool), V ∈ P ∧
      ∀ x : List Bool, x ∈ L ↔
        ∀ u : List Bool, u.length = C * (x.length + 1) ^ c → x ++ u ∈ V := by
  classical
  constructor
  · rintro ⟨C, c, V, hV, hmem⟩
    refine ⟨C, c, Vᶜ, compl_mem_P hV, fun x => ?_⟩
    have hx : x ∉ L ↔ ∃ u : List Bool,
        u.length = C * (x.length + 1) ^ c ∧ x ++ u ∈ V := hmem x
    change x ∈ L ↔ ∀ u : List Bool,
      u.length = C * (x.length + 1) ^ c → x ++ u ∉ V
    simpa only [not_not, not_exists, not_and] using not_congr hx
  · rintro ⟨C, c, V, hV, hmem⟩
    refine ⟨C, c, Vᶜ, compl_mem_P hV, fun x => ?_⟩
    change x ∉ L ↔ ∃ u : List Bool,
      u.length = C * (x.length + 1) ^ c ∧ x ++ u ∉ V
    simpa only [not_forall, exists_prop] using not_congr (hmem x)

/-- **`P ⊆ NP ∩ coNP`** [AB09, Exercise 2.23].

**Proof sketch.** `P ⊆ NP` is `Complexity.P_subset_NP`; for the `coNP` half,
`L ∈ P` gives `Lᶜ ∈ P ⊆ NP` by `Complexity.compl_mem_P`, i.e. `L ∈ coNP`. -/
theorem P_subset_NP_inter_coNP : P ⊆ NP ∩ coNP := by
  intro L hL
  exact ⟨P_subset_NP hL, P_subset_NP (compl_mem_P hL)⟩

/-- **If `P = NP` then `NP = coNP`** [AB09, Exercise 2.25].

**Proof sketch.** Under `P = NP`: `L ∈ NP → L ∈ P → Lᶜ ∈ P → Lᶜ ∈ NP → L ∈ coNP`
by `Complexity.compl_mem_P`, and symmetrically `L ∈ coNP → Lᶜ ∈ NP = P → L ∈ P =
NP` by closing under complement once more. -/
theorem NP_eq_coNP_of_P_eq_NP (h : P = NP) : NP = coNP := by
  apply Set.Subset.antisymm
  · intro L hL
    change Lᶜ ∈ NP
    rw [← h] at hL ⊢
    exact compl_mem_P hL
  · intro L hL
    change Lᶜ ∈ NP at hL
    rw [← h] at hL ⊢
    simpa only [compl_compl] using compl_mem_P hL

end Complexity
