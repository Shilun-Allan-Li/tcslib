/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Logspace.InputAccess

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bounded runs and counting loops of abstract register machines

The guard `Complexity.LogProg.GuardLe A x B` of bounded runs of an abstract register machine
(`Complexity.LogProg.ARM`): a configuration meets it when it satisfies the syntactic
preconditions `Complexity.LogProg.PreS` and all its registers are at most `B`. It is
definitionally the guard of the shared fragments of
`TCSlib.Complexity.SpaceComplexity.Logspace.InputAccess` (`registerCopy_loop`, …), so their
runs compose with runs through `GuardLe`. It is used by the codec checkers
(`TCSlib.Complexity.SpaceComplexity.Codec.Engine`) and the Savitch machine
(`TCSlib.Complexity.SpaceComplexity.SavitchARM`).

The file also proves run lemmas for the counting loops out of which register-machine
arithmetic is built: moving a register into one or two others (`move_run`, `move2_run`),
moving it doubled (`dmove_run`), subtracting (`sub_run`), halving a register as often as a
counter says (`halve_run`), copying through a scratch register (`copy_run`) and shifting left
by a counter (`shl_run`). Each lemma is stated for an arbitrary abstract register machine
whose instructions at the loop's labels have the loop's shape, as a run through `GuardLe`.

Infrastructure for the register-machine description of space-bounded algorithms of
[AB09, §4.1]; not itself a result of the book.

## Main definitions

* `Complexity.LogProg.GuardLe` — the guard: syntactic preconditions and registers at most
  `B`.

## Main results

* `Complexity.LogProg.GuardLe.of_preS` — introducing the guard.
* `Complexity.LogProg.reach_of_eq` — rewriting the end configuration of a run.
* `Complexity.LogProg.move_run`, `move2_run`, `dmove_run`, `sub_run`, `halve_run` — the
  single loops.
* `Complexity.LogProg.copy_run`, `shl_run` — the composite loops.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.LogProg

open Turing

variable {m d : ℕ} {Λ : Type}

/-- **The bounded-run guard**: the syntactic preconditions, and every register at most `B`. -/
abbrev GuardLe (A : ARM m d Λ) (x : List Bool) (B : ℕ) : AConf m Λ → Prop :=
  fun a => PreS A x a ∧ ∀ r, a.2.1 r ≤ B

variable {A : ARM m d Λ} {oracle : Fin d → List Bool → Bool} {x : List Bool} {B : ℕ}

/-- A configuration meeting the syntactic preconditions with registers at most `B` meets the
guard. -/
lemma GuardLe.of_preS {a : AConf m Λ} (h : PreS A x a) (hv : ∀ r, a.2.1 r ≤ B) :
    GuardLe A x B a := ⟨h, hv⟩

/-- A run whose end configuration is rewritten along an equation. -/
lemma reach_of_eq {G : AConf m Λ → Prop} {a b b' : AConf m Λ} (h : AReach A oracle x G a b)
    (e : b = b') : AReach A oracle x G a b' := e ▸ h

/-! ## Counting loops -/

/-- **Moving a register into another**: the loop `l: jz r lx l₁; l₁: dec r l₂; l₂: inc t l`
adds `r` to `t` and clears `r`.

**Proof sketch.** Induction on the value of `r`: each round moves one unit. -/
theorem move_run {l lx l1 l2 : Λ} {r t : Fin m} (hrt : r ≠ t)
    (h0 : A l = .jz r lx l1) (h1 : A l1 = .dec r l2) (h2 : A l2 = .inc t l) :
    ∀ (k : ℕ) (v : Fin m → ℕ), v r = k → (∀ s, v s ≤ B) → v t + v r ≤ B →
    AReach A oracle x (GuardLe A x B) (some l, v, none)
      (some lx, Function.update (Function.update v r 0) t (v t + v r), none) := by
  intro k
  induction k with
  | zero =>
    intro v hk hv _
    refine AReach.step ⟨by simp [PreS, h0], hv⟩ ?_
    have e : Function.update (Function.update v r 0) t (v t + v r) = v := by
      funext s
      by_cases hs : s = t
      · subst hs; simp [hk]
      · by_cases hs' : s = r
        · subst hs'; simp [hs, hk]
        · simp [hs, hs']
    rw [e]
    simp only [astep, h0, hk, ↓reduceIte]
    exact AReach.refl _
  | succ k ih =>
    intro v hk hv hb
    refine AReach.step ⟨by simp [PreS, h0], hv⟩ ?_
    simp only [astep, h0, hk, Nat.add_one_ne_zero, ↓reduceIte]
    refine AReach.step ⟨by simp [PreS, h1], hv⟩ ?_
    simp only [astep, h1, hk, Nat.add_sub_cancel]
    refine AReach.step ⟨by simp [PreS, h2], fun s => ?_⟩ ?_
    · by_cases hs : s = r
      · subst hs; simp; omega
      · simp [hs]; exact hv s
    simp only [astep, h2, Function.update_of_ne (Ne.symm hrt)]
    have hb2 : ∀ s, Function.update (Function.update v r k) t (v t + 1) s ≤ B := by
      intro s
      by_cases hs : s = t
      · subst hs; simp; omega
      · by_cases hs' : s = r
        · subst hs'; simp [hs]; omega
        · simp [hs, hs']; exact hv s
    refine reach_of_eq (ih _ (by simp [hrt]) hb2 (by simp [hrt]; omega)) ?_
    · congr 2
      funext s
      by_cases hs : s = t
      · subst hs; simp [hrt]; omega
      · by_cases hs' : s = r
        · subst hs'; simp [hs]
        · simp [hs, hs']

/-- Close a goal about updated register files by cases on the register. -/
macro "upd_tac" : tactic =>
  `(tactic| (funext s; simp only [Function.update_apply]; split_ifs <;> subst_vars <;>
    (try simp_all) <;> omega))

/-- **Moving a register into two others**: the loop
`l: jz r lx l₁; l₁: dec r l₂; l₂: inc t l₃; l₃: inc t' l` adds `r` to `t` and to `t'` and
clears `r`.

**Proof sketch.** Induction on the value of `r`: each round moves one unit into both. -/
theorem move2_run {l lx l1 l2 l3 : Λ} {r t t' : Fin m} (hrt : r ≠ t) (hrt' : r ≠ t')
    (htt : t ≠ t')
    (h0 : A l = .jz r lx l1) (h1 : A l1 = .dec r l2) (h2 : A l2 = .inc t l3)
    (h3 : A l3 = .inc t' l) :
    ∀ (k : ℕ) (v : Fin m → ℕ), v r = k → (∀ s, v s ≤ B) → v t + v r ≤ B → v t' + v r ≤ B →
    AReach A oracle x (GuardLe A x B) (some l, v, none)
      (some lx, Function.update (Function.update (Function.update v r 0) t (v t + v r)) t'
        (v t' + v r), none) := by
  intro k
  induction k with
  | zero =>
    intro v hk hv _ _
    refine AReach.step ⟨by simp [PreS, h0], hv⟩ ?_
    have e : Function.update (Function.update (Function.update v r 0) t (v t + v r)) t'
        (v t' + v r) = v := by upd_tac
    rw [e]
    simp only [astep, h0, hk, ↓reduceIte]
    exact AReach.refl _
  | succ k ih =>
    intro v hk hv hb hb'
    have hr := hv r
    refine AReach.step ⟨by simp [PreS, h0], hv⟩ ?_
    simp only [astep, h0, hk, Nat.add_one_ne_zero, ↓reduceIte]
    refine AReach.step ⟨by simp [PreS, h1], hv⟩ ?_
    simp only [astep, h1, hk, Nat.add_sub_cancel]
    have b1 := register_update_le _ r _ _ hv (show k ≤ B by omega)
    refine AReach.step ⟨by simp [PreS, h2], b1⟩ ?_
    simp only [astep, h2]
    have b2 := register_update_le _ t _ _ b1 (show Function.update v r k t + 1 ≤ B by
      simp [Ne.symm hrt]; omega)
    refine AReach.step ⟨by simp [PreS, h3], b2⟩ ?_
    simp only [astep, h3]
    have b3 := register_update_le _ t' _ _ b2 (show Function.update (Function.update v r k) t
        (Function.update v r k t + 1) t' + 1 ≤ B by
      simp [Ne.symm hrt', Ne.symm htt]; omega)
    refine reach_of_eq (ih _ (by simp [hrt, hrt']) b3
      (by simp [hrt, hrt', htt, Ne.symm htt, Ne.symm hrt, Ne.symm hrt']; omega)
      (by simp [hrt, hrt', Ne.symm htt, Ne.symm hrt, Ne.symm hrt']; omega)) ?_
    congr 2
    upd_tac

/-- **Moving a register doubled**: the loop
`l: jz r lx l₁; l₁: dec r l₂; l₂: inc t l₃; l₃: inc t l` adds `2r` to `t` and clears `r`.

**Proof sketch.** Induction on the value of `r`: each round moves one unit twice. -/
theorem dmove_run {l lx l1 l2 l3 : Λ} {r t : Fin m} (hrt : r ≠ t)
    (h0 : A l = .jz r lx l1) (h1 : A l1 = .dec r l2) (h2 : A l2 = .inc t l3)
    (h3 : A l3 = .inc t l) :
    ∀ (k : ℕ) (v : Fin m → ℕ), v r = k → (∀ s, v s ≤ B) → v t + 2 * v r ≤ B →
    AReach A oracle x (GuardLe A x B) (some l, v, none)
      (some lx, Function.update (Function.update v r 0) t (v t + 2 * v r), none) := by
  intro k
  induction k with
  | zero =>
    intro v hk hv _
    refine AReach.step ⟨by simp [PreS, h0], hv⟩ ?_
    have e : Function.update (Function.update v r 0) t (v t + 2 * v r) = v := by upd_tac
    rw [e]
    simp only [astep, h0, hk, ↓reduceIte]
    exact AReach.refl _
  | succ k ih =>
    intro v hk hv hb
    have hr := hv r
    refine AReach.step ⟨by simp [PreS, h0], hv⟩ ?_
    simp only [astep, h0, hk, Nat.add_one_ne_zero, ↓reduceIte]
    refine AReach.step ⟨by simp [PreS, h1], hv⟩ ?_
    simp only [astep, h1, hk, Nat.add_sub_cancel]
    have b1 := register_update_le _ r _ _ hv (show k ≤ B by omega)
    refine AReach.step ⟨by simp [PreS, h2], b1⟩ ?_
    simp only [astep, h2]
    have b2 := register_update_le _ t _ _ b1 (show Function.update v r k t + 1 ≤ B by
      simp [Ne.symm hrt]; omega)
    refine AReach.step ⟨by simp [PreS, h3], b2⟩ ?_
    simp only [astep, h3]
    have b3 := register_update_le _ t _ _ b2 (show Function.update (Function.update v r k) t
        (Function.update v r k t + 1) t + 1 ≤ B by
      simp [Ne.symm hrt]; omega)
    refine reach_of_eq (ih _ (by simp [hrt]) b3 (by simp [hrt, Ne.symm hrt]; omega)) ?_
    congr 2
    upd_tac

/-- **Subtracting a register**: the loop `l: jz q lx l₁; l₁: dec q l₂; l₂: dec r l`
subtracts `q` from `r` (truncated) and clears `q`.

**Proof sketch.** Induction on the value of `q`: each round removes one unit. -/
theorem sub_run {l lx l1 l2 : Λ} {q r : Fin m} (hqr : q ≠ r)
    (h0 : A l = .jz q lx l1) (h1 : A l1 = .dec q l2) (h2 : A l2 = .dec r l) :
    ∀ (k : ℕ) (v : Fin m → ℕ), v q = k → (∀ s, v s ≤ B) →
    AReach A oracle x (GuardLe A x B) (some l, v, none)
      (some lx, Function.update (Function.update v q 0) r (v r - v q), none) := by
  intro k
  induction k with
  | zero =>
    intro v hk hv
    refine AReach.step ⟨by simp [PreS, h0], hv⟩ ?_
    have e : Function.update (Function.update v q 0) r (v r - v q) = v := by upd_tac
    rw [e]
    simp only [astep, h0, hk, ↓reduceIte]
    exact AReach.refl _
  | succ k ih =>
    intro v hk hv
    refine AReach.step ⟨by simp [PreS, h0], hv⟩ ?_
    simp only [astep, h0, hk, Nat.add_one_ne_zero, ↓reduceIte]
    refine AReach.step ⟨by simp [PreS, h1], hv⟩ ?_
    simp only [astep, h1, hk, Nat.add_sub_cancel]
    have b1 := register_update_le _ q _ _ hv (show k ≤ B by have := hv q; omega)
    refine AReach.step ⟨by simp [PreS, h2], b1⟩ ?_
    simp only [astep, h2]
    have b2 := register_update_le _ r _ _ b1 (show Function.update v q k r - 1 ≤ B by
      simp [Ne.symm hqr]; have := hv r; omega)
    refine reach_of_eq (ih _ (by simp [hqr]) b2) ?_
    congr 2
    upd_tac

/-- **Halving a register as often as a counter says**: the loop
`l: jz c lx l₁; l₁: dec c l₂; l₂: half r l` divides `r` by `2 ^ c` and clears `c`.

**Proof sketch.** Induction on the value of `c`: `⌊⌊r / 2⌋ / 2 ^ k⌋ = ⌊r / 2 ^ (k + 1)⌋`. -/
theorem halve_run {l lx l1 l2 : Λ} {c r : Fin m} (hcr : c ≠ r)
    (h0 : A l = .jz c lx l1) (h1 : A l1 = .dec c l2) (h2 : A l2 = .half r l) :
    ∀ (k : ℕ) (v : Fin m → ℕ), v c = k → (∀ s, v s ≤ B) →
    AReach A oracle x (GuardLe A x B) (some l, v, none)
      (some lx, Function.update (Function.update v c 0) r (v r / 2 ^ v c), none) := by
  intro k
  induction k with
  | zero =>
    intro v hk hv
    refine AReach.step ⟨by simp [PreS, h0], hv⟩ ?_
    have e : Function.update (Function.update v c 0) r (v r / 2 ^ v c) = v := by upd_tac
    rw [e]
    simp only [astep, h0, hk, ↓reduceIte]
    exact AReach.refl _
  | succ k ih =>
    intro v hk hv
    refine AReach.step ⟨by simp [PreS, h0], hv⟩ ?_
    simp only [astep, h0, hk, Nat.add_one_ne_zero, ↓reduceIte]
    refine AReach.step ⟨by simp [PreS, h1], hv⟩ ?_
    simp only [astep, h1, hk, Nat.add_sub_cancel]
    have hb1 : ∀ s, Function.update v c k s ≤ B :=
      register_update_le _ _ _ _ hv (show k ≤ B by have := hv c; omega)
    refine AReach.step ⟨by simp [PreS, h2], hb1⟩ ?_
    simp only [astep, h2]
    have hb2 : ∀ s, Function.update (Function.update v c k) r (Function.update v c k r / 2) s
        ≤ B := by
      intro s
      by_cases hs : s = r
      · subst hs; simp [Ne.symm hcr]; exact (Nat.div_le_self _ _).trans (hv _)
      · simp only [Function.update_of_ne hs]; exact hb1 s
    refine reach_of_eq (ih _ (by simp [hcr]) hb2) ?_
    congr 2
    funext s
    by_cases hs : s = r
    · subst hs
      simp [hcr, Ne.symm hcr, Nat.div_div_eq_div_mul, pow_succ, mul_comm]
    · by_cases hs' : s = c
      · subst hs'; simp [hs]
      · simp [hs, hs']

/-- **Copying a register through a scratch register**: the loops
`l: jz src l₄ l₁; l₁: dec src l₂; l₂: inc dst l₃; l₃: inc z l` and
`l₄: jz z lx l₅; l₅: dec z l₆; l₆: inc src l₄`, with `z` clear, add `src` to `dst` and leave
everything else unchanged.

**Proof sketch.** `move2_run` moves `src` into `dst` and `z`, `move_run` moves `z` back. -/
theorem copy_run {l l1 l2 l3 l4 l5 l6 lx : Λ} {src dst z : Fin m} (h1 : src ≠ dst)
    (h2 : src ≠ z) (h3 : dst ≠ z)
    (a0 : A l = .jz src l4 l1) (a1 : A l1 = .dec src l2) (a2 : A l2 = .inc dst l3)
    (a3 : A l3 = .inc z l) (a4 : A l4 = .jz z lx l5) (a5 : A l5 = .dec z l6)
    (a6 : A l6 = .inc src l4)
    (v : Fin m → ℕ) (hz : v z = 0) (hv : ∀ s, v s ≤ B) (hb : v dst + v src ≤ B) :
    AReach A oracle x (GuardLe A x B) (some l, v, none)
      (some lx, Function.update v dst (v dst + v src), none) := by
  refine (move2_run h1 h2 h3 a0 a1 a2 a3 _ v rfl hv hb (by have := hv src; omega)).trans ?_
  have b1 := register_update_le _ z _ _
    (register_update_le _ dst _ _ (register_update_le _ src _ _ hv (Nat.zero_le B)) hb)
    (show v z + v src ≤ B by have := hv src; omega)
  refine reach_of_eq (move_run (Ne.symm h2) a4 a5 a6 _ _ rfl b1
    (by simp [h1, h2, hz]; exact hv src)) ?_
  congr 2
  upd_tac

/-- **Shifting a register left as often as a counter says**: the loops
`l: jz c lx l₁; l₁: dec c l₂`, then `l₂ … l₅` moving `r` doubled into `z` (exit `l₆`), then
`l₆ … l₈` moving `z` back into `r` (exit `l`), with `z` clear, multiply `r` by `2 ^ c` and
clear `c`.

**Proof sketch.** Induction on the value of `c`: each round doubles `r` (`dmove_run`,
`move_run`). -/
theorem shl_run {l l1 l2 l3 l4 l5 l6 l7 l8 lx : Λ} {c r z : Fin m} (hcr : c ≠ r) (hcz : c ≠ z)
    (hrz : r ≠ z)
    (a0 : A l = .jz c lx l1) (a1 : A l1 = .dec c l2) (a2 : A l2 = .jz r l6 l3)
    (a3 : A l3 = .dec r l4) (a4 : A l4 = .inc z l5) (a5 : A l5 = .inc z l2)
    (a6 : A l6 = .jz z l l7) (a7 : A l7 = .dec z l8) (a8 : A l8 = .inc r l6) :
    ∀ (k : ℕ) (v : Fin m → ℕ), v c = k → v z = 0 → (∀ s, v s ≤ B) → v r * 2 ^ v c ≤ B →
    AReach A oracle x (GuardLe A x B) (some l, v, none)
      (some lx, Function.update (Function.update v c 0) r (v r * 2 ^ v c), none) := by
  intro k
  induction k with
  | zero =>
    intro v hk _ hv _
    refine AReach.step ⟨by simp [PreS, a0], hv⟩ ?_
    have e : Function.update (Function.update v c 0) r (v r * 2 ^ v c) = v := by
      funext s
      by_cases hs : s = r
      · subst hs; simp [hk]
      · by_cases hs' : s = c
        · subst hs'; simp [hs, hk]
        · simp [hs, hs']
    rw [e]
    simp only [astep, a0, hk, ↓reduceIte]
    exact AReach.refl _
  | succ k ih =>
    intro v hk hz hv hb
    have h2 : 2 * v r ≤ B := by
      rw [hk, pow_succ] at hb
      have : 2 ≤ 2 ^ k * 2 := by have := Nat.one_le_two_pow (n := k); omega
      calc 2 * v r ≤ v r * (2 ^ k * 2) := by rw [mul_comm]; exact Nat.mul_le_mul_left _ this
        _ ≤ B := hb
    refine AReach.step ⟨by simp [PreS, a0], hv⟩ ?_
    simp only [astep, a0, hk, Nat.add_one_ne_zero, ↓reduceIte]
    refine AReach.step ⟨by simp [PreS, a1], hv⟩ ?_
    simp only [astep, a1, hk, Nat.add_sub_cancel]
    have hv1 : ∀ s, Function.update v c k s ≤ B :=
      register_update_le _ _ _ _ hv (show k ≤ B by have := hv c; omega)
    refine (dmove_run hrz a2 a3 a4 a5 _ _ rfl hv1
      (by simp [Ne.symm hcz, Ne.symm hcr, hz]; omega)).trans ?_
    have hv2 := register_update_le _ z _ _ (register_update_le _ r _ _ hv1 (Nat.zero_le B))
      (show Function.update v c k z + 2 * Function.update v c k r ≤ B by
        simp [Ne.symm hcz, Ne.symm hcr, hz]; omega)
    refine (move_run (Ne.symm hrz) a6 a7 a8 _ _ rfl hv2
      (by simp [hrz, Ne.symm hcz, Ne.symm hcr, hz]; omega)).trans ?_
    have hv3 : ∀ s, Function.update (Function.update (Function.update (Function.update
        (Function.update v c k) r 0) z (Function.update v c k z + 2 * Function.update v c k r))
        z 0) r (Function.update (Function.update (Function.update v c k) r 0) z
        (Function.update v c k z + 2 * Function.update v c k r) r +
        Function.update (Function.update (Function.update v c k) r 0) z
        (Function.update v c k z + 2 * Function.update v c k r) z) s ≤ B :=
      register_update_le _ _ _ _ (register_update_le _ _ _ _ hv2 (Nat.zero_le B)) (by
        simp [hrz, Ne.symm hcz, Ne.symm hcr, hz]; omega)
    refine reach_of_eq (ih _ (by simp [hcr, hcz]) (by simp [hrz, Ne.symm hrz]) hv3 ?_) ?_
    · simp [hcr, hcz, hrz, Ne.symm hcz, Ne.symm hcr, hz]
      rw [hk, pow_succ] at hb
      calc 2 * v r * 2 ^ k = v r * (2 ^ k * 2) := by ring
        _ ≤ B := hb
    · congr 2
      funext s
      by_cases hs : s = r
      · subst hs
        simp [hcr, hcz, hrz, Ne.symm hcz, Ne.symm hcr, hz, pow_succ]; ring
      · by_cases hs' : s = c
        · subst hs'; simp [hs, hcz]
        · by_cases hs'' : s = z
          · subst hs''; simp [hs, hs', hz]
          · simp [hs, hs', hs'']

end Complexity.LogProg
