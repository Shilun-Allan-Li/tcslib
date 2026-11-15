/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import TCSlib.Cryptography.Randomness.Learning.Law
/- DLC-SEAL Randomness_Learning_Random: whole-file closure seal of `TCSlib/Cryptography/Randomness/Learning/Random.lean`, variant B (PolyExpr.eval sealed), coe (projection coercions open). -/
/-- Strip leading lambdas (seal harness). -/
partial def dlcStripLam : Lean.Expr → Lean.Expr
  | .lam _ _ b _ => dlcStripLam b
  | e => e

set_option maxHeartbeats 0 in
run_cmd do
  let env ← Lean.getEnv
  let excl : List Lean.Name := []
  let coeOpen : Bool := true
  let coeClasses : List Lean.Name := [`CoeFun, `Coe, `CoeSort, `CoeOut, `CoeTail, `CoeHead,
    `CoeTC, `CoeHTCT, `CoeDep]
  let mut sealed : Array Lean.Name := #[]
  let mut abbrevs : Nat := 0
  let mut already : Nat := 0
  let mut excluded : Nat := 0
  let mut coeExcl : Array Lean.Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[mi.toNat]!
    unless (`TCSlib).isPrefixOf m do continue
    let .defnInfo d := ci | continue
    if excl.contains n then
      excluded := excluded + 1
      continue
    if coeOpen && Lean.Meta.isInstanceCore env n then
      let isCoeCls := match d.type.getForallBody.getAppFn.constName? with
        | some c => coeClasses.contains c
        | none => false
      if isCoeCls then
        let body := dlcStripLam d.value
        let args := body.getAppArgs
        let projArg := match args.back? with
          | some a => match (dlcStripLam a).getAppFn.constName? with
            | some p => (env.getProjectionFnInfo? p).isSome
            | none => false
          | none => false
        if projArg then
          coeExcl := coeExcl.push n
          continue
    match d.hints with
    | .abbrev =>
      abbrevs := abbrevs + 1
      continue
    | _ => pure ()
    let st ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    if st == .irreducible then
      already := already + 1
      sealed := sealed.push n
      continue
    Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $(Lean.mkIdent n):ident))
    let st' ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless st' == .irreducible do throwError "DLC-SEAL: not sealed {n}"
    sealed := sealed.push n
  Lean.modifyEnv fun cur =>
    Lean.Meta.globalInstanceExtension.modifyState cur fun s => sealed.foldl (fun s n => s.erase n) s
  let env' ← Lean.getEnv
  for n in sealed do
    if Lean.Meta.isGlobalInstance env' n then throwError "DLC-SEAL: instance unfolding kept for {n}"
  Lean.logInfo m!"DLC-SEAL Randomness_Learning_Random: sealed={sealed.size} (already irreducible {already}) abbrev-excluded={abbrevs} excluded={excluded} coe-excluded={coeExcl.size} {coeExcl.toList}"


set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# With a random function, no learner predicts better than `½ ± m/2^n`

Step 2 of [PS10, Theorem 179.1, proof]: in the game with a uniform random function
`R : {0,1}^n → {0,1}^n` in place of the keyed family, every learner `ℓ` predicts the first bit of
`R x` with probability within `m/2^n` of `½`, for `n ≥ 1` (`abs_gameProb_random_sub_half_le`).

**Proof.** Fix the examples `s`, the coins `r` and the fresh point `x`. If `x` is none of the
examples, flipping the first bit of `R x` (`flipAt`, an involution of the random functions) keeps
the labelled examples and negates the label of `x`, so it exchanges the winning and the losing
functions: the probability over `R` is exactly `½` (`uprob_flip_half`). Otherwise the probability
is between `0` and `1`. So the game probability is within `Pr[x ∈ s]` of `½`, and
`Pr[x ∈ s] ≤ Σ_j Pr[x = s_j] = m · 2^{-n}` (`uprob_exists_le`, `uprob_eq_point`).

## Main definitions

* `LearnPRF.flip0`, `LearnPRF.flipAt`: flipping the first bit of a string, and of a function's
  value at a point.

## Main results

* `LearnPRF.firstBit_flip0`, `LearnPRF.flipAt_involutive`.
* `LearnPRF.uprob_flip_half`: at a fresh point, the prediction wins with probability `½`.
* `LearnPRF.uprob_eq_point`: a uniform point hits a given point with probability `2^{-n}`.
* `LearnPRF.abs_gameProb_random_sub_half_le`: the bound `|gameProb − ½| ≤ m/2^n`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §8.1, Theorem 179.1 (book p. 179).
-/

namespace TCSlib.Cryptography.Randomness.LearnPRF

open Complexity TCSlib.Cryptography TCSlib.LearningTheory.PAC Finset

section Random

variable {n : ℕ} (hn : 0 < n)

/-- **Flipping the first bit** of an `n`-bit string (`n ≥ 1`):
`flip0 hn y = update y 0 (!y 0)`. -/
def flip0 (y : Fin n → Bool) : Fin n → Bool := Function.update y ⟨0, hn⟩ (!y ⟨0, hn⟩)

/-- `flip0 hn y = Function.update y ⟨0, hn⟩ (!y ⟨0, hn⟩)`. -/
theorem flip0_eq (y : Fin n → Bool) : flip0 hn y = Function.update y ⟨0, hn⟩ (!y ⟨0, hn⟩) := rfl

/-- Flipping twice is the identity: `flip0 hn (flip0 hn y) = y`. -/
theorem flip0_flip0 (y : Fin n → Bool) : flip0 hn (flip0 hn y) = y := by
  rw [flip0_eq, flip0_eq, Function.update_self, Function.update_idem, Bool.not_not,
    Function.update_eq_self]

/-- The first bit of an `n`-bit string with `n ≥ 1` is its bit `0`:
`firstBit y = y ⟨0, hn⟩`. -/
theorem firstBit_of_pos (y : Fin n → Bool) : firstBit y = y ⟨0, hn⟩ := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [firstBit_eq, List.ofFn_succ, List.headD_cons]
  rfl

/-- Flipping the first bit negates it: `firstBit (flip0 hn y) = !firstBit y`. -/
theorem firstBit_flip0 (y : Fin n → Bool) : firstBit (flip0 hn y) = !firstBit y := by
  rw [firstBit_of_pos hn, firstBit_of_pos hn, flip0_eq, Function.update_self]

/-- **Flipping the first bit of a function's value at `x`:**
`flipAt hn x R = update R x (flip0 hn (R x))`. -/
def flipAt (x : Fin n → Bool) (R : (Fin n → Bool) → (Fin n → Bool)) :
    (Fin n → Bool) → (Fin n → Bool) :=
  Function.update R x (flip0 hn (R x))

/-- `flipAt hn x R = Function.update R x (flip0 hn (R x))`. -/
theorem flipAt_eq (x : Fin n → Bool) (R : (Fin n → Bool) → (Fin n → Bool)) :
    flipAt hn x R = Function.update R x (flip0 hn (R x)) := rfl

/-- `flipAt hn x` is an involution. -/
theorem flipAt_involutive (x : Fin n → Bool) : Function.Involutive (flipAt hn x) := by
  intro R
  rw [flipAt_eq, flipAt_eq, Function.update_self, flip0_flip0, Function.update_idem,
    Function.update_eq_self]

include hn in
/-- **At a fresh point the prediction wins with probability `½`:** if `x` is none of the
examples `s`, then for every learner `ℓ` and coins `r`, the uniform probability over `R` that
`ℓ (label (firstBit ∘ R) s) r x == firstBit (R x)` is `½`.

**Proof sketch.** `flipAt hn x` is a bijection of the functions (`flipAt_involutive`), so it
preserves the probability (`uprob_comp_equiv`). It keeps the labels of the examples
(`Function.update_of_ne`) and negates the label of `x` (`firstBit_flip0`), so it maps the event to
its complement; hence `p = 1 − p` (`uprob_not`). -/
theorem uprob_flip_half {m : ℕ} {ρ : Type*}
    (ℓ : (Fin m → (Fin n → Bool) × Bool) → ρ → (Fin n → Bool) → Bool) (s : Fin m → Fin n → Bool)
    (r : ρ) (x : Fin n → Bool) (hx : ∀ j, s j ≠ x) :
    uprob (fun R : (Fin n → Bool) → (Fin n → Bool) =>
      (ℓ (label (fun z => firstBit (R z)) s) r x == firstBit (R x)) = true) = 1 / 2 := by
  set σ := Function.Involutive.toPerm (flipAt hn x) (flipAt_involutive hn x) with hσ
  have h1 := uprob_comp_equiv σ (fun R =>
    (ℓ (label (fun z => firstBit (R z)) s) r x == firstBit (R x)) = true)
  have h2 : (fun R : (Fin n → Bool) → (Fin n → Bool) =>
      (ℓ (label (fun z => firstBit (σ R z)) s) r x ==
        firstBit (σ R x)) = true) =
      fun R => ¬ (ℓ (label (fun z => firstBit (R z)) s) r x == firstBit (R x)) = true := by
    funext R
    have hl : label (fun z => firstBit (σ R z)) s =
        label (fun z => firstBit (R z)) s := by
      funext j
      rw [label_apply, label_apply, hσ, Function.Involutive.coe_toPerm, flipAt_eq,
        Function.update_of_ne (hx j)]
    rw [hl, hσ, Function.Involutive.coe_toPerm, flipAt_eq, Function.update_self, firstBit_flip0]
    cases ℓ (label (fun z => firstBit (R z)) s) r x <;> cases firstBit (R x) <;> decide
  rw [h2, uprob_not] at h1
  linarith

/-- **A uniform point hits a given point with probability `2^{-n}`:**
`uprob (fun x : {0,1}^n => y = x) = 1 / 2^n`. -/
theorem uprob_eq_point (y : Fin n → Bool) :
    uprob (fun x : Fin n → Bool => y = x) = 1 / 2 ^ n := by
  classical
  rw [uprob_eq_card_filter, Finset.filter_eq, if_pos (Finset.mem_univ y), Finset.card_singleton,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_one, Nat.cast_pow,
    Nat.cast_two]

include hn in
/-- **With a random function the prediction is within `m/2^n` of `½`** [PS10, Theorem 179.1,
proof, step 2]: for `n ≥ 1`, every learner `ℓ` and `m` examples,
`|gameProb m (fun R => R) ℓ − ½| ≤ m / 2^n`.

**Proof sketch.** Put the function last (`uprob_comp_equiv`) and average over it first
(`uprob_prod`): for fixed `((s, r), x)` the probability `p` is `½` when `x` is fresh
(`uprob_flip_half`) and in `[0, 1]` otherwise, so `|p − ½| ≤ [x ∈ s]`. Averaging,
`|gameProb − ½| ≤ Pr[∃ j, s_j = x]`, which the union bound (`uprob_exists_le`) bounds by
`Σ_j Pr[s_j = x] = m · 2^{-n}` (`uprob_prod`, `uprob_eq_point`). -/
theorem abs_gameProb_random_sub_half_le {ρ : Type*} [Fintype ρ] [Nonempty ρ] (m : ℕ)
    (ℓ : (Fin m → (Fin n → Bool) × Bool) → ρ → (Fin n → Bool) → Bool) :
    |gameProb m (fun R : (Fin n → Bool) → (Fin n → Bool) => R) ℓ - 1 / 2| ≤ m / 2 ^ n := by
  classical
  -- the random function last
  let e : (((Fin m → Fin n → Bool) × ρ) × (Fin n → Bool)) × ((Fin n → Bool) → (Fin n → Bool)) ≃
      (((Fin n → Bool) → (Fin n → Bool)) × ((Fin m → Fin n → Bool) × ρ)) × (Fin n → Bool) :=
    { toFun := fun w => ((w.2, w.1.1), w.1.2)
      invFun := fun w => ((w.1.2, w.2), w.1.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  set p : ((Fin m → Fin n → Bool) × ρ) × (Fin n → Bool) → ℝ := fun t =>
    uprob (fun R : (Fin n → Bool) → (Fin n → Bool) =>
      (ℓ (label (fun z => firstBit (R z)) t.1.1) t.1.2 t.2 == firstBit (R t.2)) = true) with hp
  have hgame : gameProb m (fun R : (Fin n → Bool) → (Fin n → Bool) => R) ℓ = uexp p := by
    rw [gameProb_eq, ← uprob_comp_equiv e, uprob_prod]
    rfl
  -- the bad event: the fresh point is an example
  set bad : ((Fin m → Fin n → Bool) × ρ) × (Fin n → Bool) → Prop :=
    fun t => ∃ j ∈ (Finset.univ : Finset (Fin m)), t.1.1 j = t.2 with hbad
  have hpt : ∀ t, |p t - 1 / 2| ≤ if bad t then 1 else 0 := by
    intro t
    by_cases hb : bad t
    · rw [if_pos hb, abs_le]
      have h0 := uprob_nonneg (fun R : (Fin n → Bool) → (Fin n → Bool) =>
        (ℓ (label (fun z => firstBit (R z)) t.1.1) t.1.2 t.2 == firstBit (R t.2)) = true)
      have h1 := uprob_le_one (fun R : (Fin n → Bool) → (Fin n → Bool) =>
        (ℓ (label (fun z => firstBit (R z)) t.1.1) t.1.2 t.2 == firstBit (R t.2)) = true)
      constructor <;> linarith
    · rw [if_neg hb, hp]
      beta_reduce
      have hx : ∀ j, t.1.1 j ≠ t.2 := fun j hj => hb ⟨j, Finset.mem_univ j, hj⟩
      rw [uprob_flip_half hn ℓ t.1.1 t.1.2 t.2 hx, sub_self, abs_zero]
  have hcard : (0 : ℝ) < Fintype.card (((Fin m → Fin n → Bool) × ρ) × (Fin n → Bool)) := by
    exact_mod_cast Fintype.card_pos
  have hdev : |uexp p - 1 / 2| ≤ uprob bad := by
    rw [uprob_eq_uexp, uexp_def, uexp_def]
    have hhalf : (1 : ℝ) / 2 = (∑ _t : ((Fin m → Fin n → Bool) × ρ) × (Fin n → Bool),
        (1 : ℝ) / 2) / Fintype.card (((Fin m → Fin n → Bool) × ρ) × (Fin n → Bool)) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
    rw [hhalf, ← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hcard]
    gcongr
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => hpt t)
  -- the union bound
  have hj : ∀ j : Fin m, uprob (fun t : ((Fin m → Fin n → Bool) × ρ) × (Fin n → Bool) =>
      t.1.1 j = t.2) = 1 / 2 ^ n := by
    intro j
    rw [uprob_prod]
    simp only [uprob_eq_point, uexp_def, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have : (0 : ℝ) < Fintype.card ((Fin m → Fin n → Bool) × ρ) := by
      exact_mod_cast Fintype.card_pos
    field_simp
  have hunion := uprob_exists_le (Finset.univ : Finset (Fin m))
    (fun j (t : ((Fin m → Fin n → Bool) × ρ) × (Fin n → Bool)) => t.1.1 j = t.2)
  simp only [hj, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hunion
  rw [hgame]
  refine hdev.trans (hunion.trans (le_of_eq ?_))
  ring

end Random

end TCSlib.Cryptography.Randomness.LearnPRF
