/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Tactic.FinCases
import TCSlib.Complexity.SpaceComplexity.Machines.NARMProof

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A sanity example of a nondeterministic abstract register machine

The language of well-formed inputs `⟨1ⁿ, w⟩` (`Complexity.LogProg.ValidPlain`), decided by
guessing: the machine `Complexity.LogProg.guessValidA` first chooses a branch; on branch `1`
it checks the input format and answers `true` when it is valid, on branch `0` it answers
`false`. Some branch accepts exactly on valid inputs, so the language is in `NL`
(`Complexity.LogProg.validPlainLang_mem_NL`, by `Complexity.LogProg.narm_decides`). The
language is of course in `L` already; the example only exercises the interface of
`TCSlib.Complexity.SpaceComplexity.Machines.NARM` and
`TCSlib.Complexity.SpaceComplexity.Machines.NARMProof` (the combinators `NHalts.choose`,
`NHalts.det`, `nans_choose`, `nans_det`, `nans_halted`).

This is a test of infrastructure for [AB09, §4.3], not a result of the book.

## Main definitions

* `Complexity.LogProg.validPlainLang`, `Complexity.LogProg.guessValidA`.

## Main results

* `Complexity.LogProg.validPlainLang_mem_NL`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3.)
-/

namespace Complexity.LogProg

open Turing

/-- The well-formed inputs `⟨1ⁿ, w⟩` with `w` a canonical binary word. -/
def validPlainLang : Language Bool := {x | ValidPlain x}

/-- The guessing machine, one register, no deciders: label `0` chooses between `1` and `2`;
label `1` checks the input format and goes to `3`; label `2` answers `false`; label `3`
answers `true`. -/
def guessValidA : NARM 1 0 (Fin 4) :=
  ![.choose 1 2, .det (.valP 0 3), .det (.ret false), .det (.ret true)]

/-- Every choice word of length `3` halts the guessing machine, through configurations with all
registers `0`. -/
lemma guessValidA_halts (x : List Bool) (G : AConf 1 (Fin 4) → Prop)
    (hG : ∀ l res, G (some l, fun _ => 0, res)) (oracle : Fin 0 → List Bool → Bool) :
    NHalts guessValidA oracle x G (some 0, fun _ => 0, none) 3 := by
  have h3 : NHalts guessValidA oracle x G (some 3, fun _ => 0, none) 1 :=
    NHalts.det (i := .ret true) rfl false (hG _ _) (by
      simpa [astep, NARM.detPart, guessValidA] using NHalts.halted _ _ 0)
  have h1 : NHalts guessValidA oracle x G (some 1, fun _ => 0, none) 2 := by
    refine NHalts.det (i := .valP 0 3) rfl false (hG _ _) ?_
    by_cases hv : ValidPlain x
    · simpa [astep, NARM.detPart, guessValidA, hv] using h3
    · simpa [astep, NARM.detPart, guessValidA, hv] using NHalts.halted _ _ 1
  have h2 : NHalts guessValidA oracle x G (some 2, fun _ => 0, none) 2 :=
    NHalts.det (i := .ret false) rfl false (hG _ _) (by
      simpa [astep, NARM.detPart, guessValidA] using NHalts.halted _ _ 1)
  exact NHalts.choose (A := guessValidA) (l := 0) (l₁ := 1) (l₀ := 2) rfl (hG _ _) h1 h2

/-- Some choice word of length `3` makes the guessing machine answer `true` iff the input is
well formed. -/
lemma guessValidA_ans (x : List Bool) (oracle : Fin 0 → List Bool → Bool) :
    NAns guessValidA oracle x (some 0, fun _ => 0, none) 3 true ↔ ValidPlain x := by
  rw [nans_choose (A := guessValidA) (l := 0) (l₁ := 1) (l₀ := 2) rfl, nans_det (i := .valP 0 3) rfl false,
    nans_det (i := .ret false) rfl false]
  by_cases hv : ValidPlain x
  · have e : astep (guessValidA.detPart false) oracle x (some 1, fun _ => 0, none) =
        (some 3, fun _ => 0, none) := by simp [astep, NARM.detPart, guessValidA, hv]
    rw [e, nans_det (i := .ret true) rfl false]
    simp [astep, NARM.detPart, guessValidA, nans_halted, hv]
  · have e : astep (guessValidA.detPart false) oracle x (some 1, fun _ => 0, none) =
        (none, fun _ => 0, some false) := by simp [astep, NARM.detPart, guessValidA, hv]
    rw [e]
    simp [astep, NARM.detPart, guessValidA, nans_halted, hv]

/-- **The well-formed inputs are in `NL`, by guessing.** A sanity check of `narm_decides`. -/
theorem validPlainLang_mem_NL : validPlainLang ∈ NL := by
  refine narm_decides guessValidA 0 (fun j => j.elim0) (fun j => j.elim0) 1 fun x => ?_
  have hpre : ∀ (l : Fin 4) (res : Option Bool), NPreS guessValidA x (some l, fun _ => 0, res) := by
    intro l res
    fin_cases l <;> simp [NPreS, PreS, NARM.detPart, guessValidA]
  have hw : (Nat.bits (0 + 1)).length ≤ 1 * logSpace x.length := by
    have : (Nat.bits (0 + 1)).length ≤ 1 := length_bits_le (by norm_num)
    have : 1 ≤ logSpace x.length := by simp [logSpace]
    omega
  exact ⟨3, guessValidA_halts x _ (fun l res => ⟨hpre l res, fun _ => hw⟩) _,
    (guessValidA_ans x _).symm⟩

end Complexity.LogProg
