/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.SavitchARM.Setup

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The outer search of the Savitch register machine

After the setup, `Complexity.LogProg.SavitchARM.A` runs a register `U` through the codes
below `K = 2 ^ w`, keeping those the initial-code decider accepts, and for each such `U` a
register `V` through the codes the accepting-code decider accepts; for each candidate pair
it evaluates the midpoint recursion at the root level `w`
(`Complexity.LogProg.SavitchARM.call_spec`) and accepts on success
(`outerV_run`, `outerU_run`). Together with the setup (`setup_run`), the machine answers
whether some initial code reaches some accepting code by midpoint reachability
(`savitch_halts`).

Infrastructure for [AB09, §4.2.1, proof of Theorem 4.14]; not itself a result of the book.

## Main definitions

* `Complexity.LogProg.SavitchARM.outerSt` — the register files of the outer search.
* `Complexity.LogProg.SavitchARM.InitO`, `AccO` — the code tests read from the oracle.

## Main results

* `Complexity.LogProg.SavitchARM.outerU_run` — the outer search.
* `Complexity.LogProg.SavitchARM.savitch_halts` — the whole run.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.2.1, Theorem 4.14.)
-/

namespace Complexity.LogProg

namespace SavitchARM

open Turing

/-- **The register files of the outer search**: after the setup, with candidate codes `u`,
`v` and midpoint register `M`. -/
def outerSt (s w u v M : ℕ) : St := { setSt s w with U := u, V := v, M := M }

/-- The initial-code test read from the oracle: decider `1` accepts `⟨x, ⟨bits u, bits s⟩⟩`. -/
def InitO (orc : Fin 4 → List Bool → Bool) (x : List Bool) (s u : ℕ) : Prop :=
  orc 1 (pairEncode x (pairEncode (Nat.bits u) (Nat.bits s))) = true

/-- The accepting-code test read from the oracle: decider `2` accepts
`⟨x, ⟨bits v, bits s⟩⟩`. -/
def AccO (orc : Fin 4 → List Bool → Bool) (x : List Bool) (s v : ℕ) : Prop :=
  orc 2 (pairEncode x (pairEncode (Nat.bits v) (Nat.bits s))) = true

section Outer

variable {s w u v M : ℕ}

/-- The `U` register of an outer-search file. -/
@[simp] lemma outerSt_U : (outerSt s w u v M).U = u := rfl
/-- The `V` register of an outer-search file. -/
@[simp] lemma outerSt_V : (outerSt s w u v M).V = v := rfl
/-- The `M` register of an outer-search file. -/
@[simp] lemma outerSt_M : (outerSt s w u v M).M = M := rfl
/-- The `I` register of an outer-search file. -/
@[simp] lemma outerSt_I : (outerSt s w u v M).I = 0 := rfl
/-- The `K` register of an outer-search file. -/
@[simp] lemma outerSt_K : (outerSt s w u v M).K = 2 ^ w := rfl
/-- The `w` register of an outer-search file. -/
@[simp] lemma outerSt_w : (outerSt s w u v M).w = w := rfl
/-- The `s` register of an outer-search file. -/
@[simp] lemma outerSt_s : (outerSt s w u v M).s = s := rfl

/-- The register files of the outer search are bounded by `2 ^ (w · w)`. -/
lemma outerSt_bd (hsw : s ≤ w) (hu : u ≤ 2 ^ w) (hv : v ≤ 2 ^ w) (hM : M ≤ 2 ^ w) :
    (outerSt s w u v M).Bd (2 ^ (w * w)) := by
  obtain ⟨f1, f2⟩ := size_facts w
  simp only [St.Bd, outerSt, setSt, St.zero]
  omega

/-- The register files of the outer search, with the level set to `w`, meet the invariant
of the root level. -/
lemma outerSt_inv (hu : u < 2 ^ w) (hv : v < 2 ^ w) (hM : M ≤ 2 ^ w) :
    Inv s w w { outerSt s w u v M with I := w } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hu, hv, hM, rfl,
    by simp [outerSt, setSt, St.zero], by simp [outerSt, setSt, St.zero]⟩

end Outer

variable {E : ℕ} {orc : Fin 4 → List Bool → Bool} {x : List Bool} {s w : ℕ}

open Classical in
/-- **The inner search**: from `OV` with candidate initial code `u` and counter `v`, the
machine answers whether some accepting code `v' ∈ [v, 2 ^ w)` has
`Reach (2 ^ w) R w u v'`, and otherwise continues as from `NU` (answering `b₀`).

**Proof sketch.** Induction on `2 ^ w - v`. At `v = 2 ^ w` the machine clears `V` and goes
to `NU`. Below, it asks decider `2` about `v`; on acceptance it sets `I := w` and runs the
recursion (`call_spec`), accepting if it answers `true`; otherwise it moves to `v + 1`. -/
theorem outerV_run (hsw : s ≤ w) (u : ℕ) (hu : u < 2 ^ w) (b₀ : Bool)
    (hNU : ∀ M ≤ 2 ^ w, AHalt (A E) orc x (GuardLe (A E) x (2 ^ (w * w)))
      (some .NU, (outerSt s w u 0 M).toV, none) b₀) :
    ∀ k v M, v + k = 2 ^ w → M ≤ 2 ^ w →
      AHalt (A E) orc x (GuardLe (A E) x (2 ^ (w * w))) (some .OV, (outerSt s w u v M).toV, none)
        (decide (∃ v', v ≤ v' ∧ v' < 2 ^ w ∧ AccO orc x s v' ∧
          Reach (2 ^ w) (Rel orc x s) w u v') || b₀) := by
  intro k
  induction k with
  | zero =>
    intro v M hk hM
    have hbd := outerSt_bd hsw hu.le (le_of_eq (by omega)) hM
    refine AHalt.step (gb_of hbd _) ?_
    regs [astep, A, outerSt_V, outerSt_K, if_pos (show v = 2 ^ w by omega)]
    refine AHalt.step (gb_of hbd _) ?_
    regs [astep, A]
    rw [decide_eq_false (by rintro ⟨v', h1, h2, -⟩; omega), Bool.false_or]
    exact hNU M hM
  | succ k ih =>
    intro v M hk hM
    have hv : v < 2 ^ w := by omega
    have hbd := outerSt_bd hsw hu.le hv.le hM
    obtain ⟨f1, f2⟩ := size_facts w
    have shift : ∀ (hn : ¬ (AccO orc x s v ∧ Reach (2 ^ w) (Rel orc x s) w u v)) (M' : ℕ),
        M' ≤ 2 ^ w → AHalt (A E) orc x (GuardLe (A E) x (2 ^ (w * w)))
          (some .NV, (outerSt s w u v M').toV, none)
          (decide (∃ v', v ≤ v' ∧ v' < 2 ^ w ∧ AccO orc x s v' ∧
            Reach (2 ^ w) (Rel orc x s) w u v') || b₀) := by
      intro hn M' hM'
      refine AHalt.step (gb_of (outerSt_bd hsw hu.le hv.le hM') _) ?_
      regs [astep, A, outerSt_V]
      have e := exists_shift (R₁ := fun m => AccO orc x s m)
        (R₂ := fun m => Reach (2 ^ w) (Rel orc x s) w u m) (a := v) (K := 2 ^ w) hn
      beta_reduce at e
      rw [← decide_eq_decide.mpr e]
      exact ih (v + 1) M' (by omega) hM'
    refine AHalt.step (gb_of hbd _) ?_
    regs [astep, A, outerSt_V, outerSt_K, if_neg (show v ≠ 2 ^ w by omega)]
    refine AHalt.step (gb_of hbd _) ?_
    simp only [astep, A, vword_whole₂]
    regs [outerSt_V, outerSt_s]
    by_cases ha : AccO orc x s v
    · have ha' : orc 2 (pairEncode x (pairEncode (Nat.bits v) (Nat.bits s))) = true := ha
      rw [if_pos ha']
      -- `root`: set `I := w` and run the recursion
      refine AHalt.step (gb_of hbd _) ?_
      regs [astep, A]
      refine (cp_run .rootW _ (by simp only [St.Bd, outerSt, setSt, St.zero]; omega) rfl
        (by regs [cpDst, cpSrc]; simp only [outerSt, setSt, St.zero]; omega)).halt ?_
      regs [cpDst, cpSrc, cpExit]
      obtain ⟨M', hM', hc⟩ := call_spec (E := E) (orc := orc) (x := x) hsw w le_rfl _
        (outerSt_inv (s := s) hu hv hM)
      refine contH (st' := { outerSt s w u v M with I := w }) (by ext <;> simp [outerSt, setSt,
        St.zero]) (hc.halt ?_)
      dsimp only
      have hbd' : St.Bd (2 ^ (w * w)) { outerSt s w u v M' with I := w } := by
        simp only [St.Bd, outerSt, setSt, St.zero]; omega
      refine AHalt.step (gb_of hbd' _) ?_
      regs [astep, A, outerSt_U, outerSt_V, outerSt_w, if_true]
      by_cases hr : Reach (2 ^ w) (Rel orc x s) w u v
      · simp only [hr, decide_true, ↓reduceIte]
        rw [decide_eq_true ⟨v, le_rfl, hv, ha, hr⟩, Bool.true_or]
        exact AHalt.ret rfl (gb_of hbd' _)
      · simp only [hr, decide_false, Bool.false_eq_true, ↓reduceIte]
        refine AHalt.step (gb_of hbd' _) ?_
        regs [astep, A]
        exact shift (fun hh => hr hh.2) M' hM'
    · have ha' : ¬ orc 2 (pairEncode x (pairEncode (Nat.bits v) (Nat.bits s))) = true := ha
      rw [if_neg ha']
      exact shift (fun hh => ha hh.1) M hM

open Classical in
/-- **The outer search**: from `OU` with candidate `u` (and `V = 0`), the machine answers
whether some initial code `u' ∈ [u, 2 ^ w)` reaches some accepting code `v < 2 ^ w` by
midpoint reachability at level `w`.

**Proof sketch.** Induction on `2 ^ w - u`. At `u = 2 ^ w` the machine rejects. Below, it
asks decider `1` about `u`; on acceptance it runs the inner search (`outerV_run`), which
falls through to `u + 1` (the induction hypothesis, through `NU`); otherwise it moves to
`u + 1` directly. -/
theorem outerU_run (hsw : s ≤ w) : ∀ k u M, u + k = 2 ^ w → M ≤ 2 ^ w →
    AHalt (A E) orc x (GuardLe (A E) x (2 ^ (w * w))) (some .OU, (outerSt s w u 0 M).toV, none)
      (decide (∃ u', u ≤ u' ∧ u' < 2 ^ w ∧ InitO orc x s u' ∧
        ∃ v < 2 ^ w, AccO orc x s v ∧ Reach (2 ^ w) (Rel orc x s) w u' v)) := by
  intro k
  induction k with
  | zero =>
    intro u M hk hM
    have hbd := outerSt_bd hsw (le_of_eq (by omega)) (Nat.zero_le _) hM
    refine AHalt.step (gb_of hbd _) ?_
    regs [astep, A, outerSt_U, outerSt_K, if_pos (show u = 2 ^ w by omega)]
    rw [decide_eq_false (by rintro ⟨u', h1, h2, -⟩; omega)]
    exact AHalt.ret rfl (gb_of hbd _)
  | succ k ih =>
    intro u M hk hM
    have hu : u < 2 ^ w := by omega
    have hbd := outerSt_bd hsw hu.le (Nat.zero_le _) hM
    have hNU : ∀ M' ≤ 2 ^ w, AHalt (A E) orc x (GuardLe (A E) x (2 ^ (w * w)))
        (some .NU, (outerSt s w u 0 M').toV, none)
        (decide (∃ u', u + 1 ≤ u' ∧ u' < 2 ^ w ∧ InitO orc x s u' ∧
          ∃ v < 2 ^ w, AccO orc x s v ∧ Reach (2 ^ w) (Rel orc x s) w u' v)) := by
      intro M' hM'
      refine AHalt.step (gb_of (outerSt_bd hsw hu.le (Nat.zero_le _) hM') _) ?_
      regs [astep, A, outerSt_U]
      exact ih (u + 1) M' (by omega) hM'
    refine AHalt.step (gb_of hbd _) ?_
    regs [astep, A, outerSt_U, outerSt_K, if_neg (show u ≠ 2 ^ w by omega)]
    refine AHalt.step (gb_of hbd _) ?_
    simp only [astep, A, vword_whole₂]
    regs [outerSt_U, outerSt_s]
    by_cases hi : InitO orc x s u
    · have hi' : orc 1 (pairEncode x (pairEncode (Nat.bits u) (Nat.bits s))) = true := hi
      rw [if_pos hi']
      have h := outerV_run hsw u hu _ hNU (2 ^ w) 0 M (by omega) hM
      have e : decide (∃ u', u ≤ u' ∧ u' < 2 ^ w ∧ InitO orc x s u' ∧
          ∃ v < 2 ^ w, AccO orc x s v ∧ Reach (2 ^ w) (Rel orc x s) w u' v) =
          (decide (∃ v', 0 ≤ v' ∧ v' < 2 ^ w ∧ AccO orc x s v' ∧
            Reach (2 ^ w) (Rel orc x s) w u v') ||
          decide (∃ u', u + 1 ≤ u' ∧ u' < 2 ^ w ∧ InitO orc x s u' ∧
            ∃ v < 2 ^ w, AccO orc x s v ∧ Reach (2 ^ w) (Rel orc x s) w u' v)) := by
        rw [Bool.eq_iff_iff]
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        constructor
        · rintro ⟨u', h1, h2, h3, v, hv, h4, h5⟩
          rcases Nat.eq_or_lt_of_le h1 with rfl | h1
          · exact Or.inl ⟨v, Nat.zero_le _, hv, h4, h5⟩
          · exact Or.inr ⟨u', h1, h2, h3, v, hv, h4, h5⟩
        · rintro (⟨v, -, hv, h4, h5⟩ | ⟨u', h1, h2, h3, h4⟩)
          · exact ⟨u, le_rfl, hu, hi, v, hv, h4, h5⟩
          · exact ⟨u', by omega, h2, h3, h4⟩
      rw [e]
      exact h
    · have hi' : ¬ orc 1 (pairEncode x (pairEncode (Nat.bits u) (Nat.bits s))) = true := hi
      rw [if_neg hi']
      have e := exists_shift (R₁ := fun m => InitO orc x s m)
        (R₂ := fun m => ∃ v < 2 ^ w, AccO orc x s v ∧ Reach (2 ^ w) (Rel orc x s) w m v)
        (a := u) (K := 2 ^ w) (fun hh => hi hh.1)
      beta_reduce at e
      rw [← decide_eq_decide.mpr e]
      exact hNU M hM

open Classical in
/-- **The run of the Savitch machine** [AB09, §4.2.1, proof of Theorem 4.14]: with
`n = |x|`, `s = (n + 2) ^ E` and `w = (n + 2) ^ (2E)`, the machine `A E` (with `E ≥ 1`),
started with all registers clear and decider `0` answering length queries, answers whether
some initial code `u < 2 ^ w` reaches some accepting code `v < 2 ^ w` by midpoint
reachability at level `w`, through register values at most `2 ^ (w · w)`.

**Proof sketch.** `setup_run` followed by `outerU_run` from `u = 0`. -/
theorem savitch_halts (hE : 1 ≤ E)
    (hq : ∀ k ≤ x.length, orc 0 (pairEncode x (Nat.bits k)) = decide (k < x.length)) :
    AHalt (A E) orc x (GuardLe (A E) x (2 ^ ((x.length + 2) ^ (2 * E) * (x.length + 2) ^ (2 * E))))
      (some .scan, fun _ => 0, none)
      (decide (∃ u < 2 ^ (x.length + 2) ^ (2 * E), InitO orc x ((x.length + 2) ^ E) u ∧
        ∃ v < 2 ^ (x.length + 2) ^ (2 * E), AccO orc x ((x.length + 2) ^ E) v ∧
          Reach (2 ^ (x.length + 2) ^ (2 * E)) (Rel orc x ((x.length + 2) ^ E))
            ((x.length + 2) ^ (2 * E)) u v)) := by
  have hsw : (x.length + 2) ^ E ≤ (x.length + 2) ^ (2 * E) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  obtain ⟨-, f2⟩ := size_facts ((x.length + 2) ^ (2 * E))
  rw [St.toV_zero]
  refine (setup_run hE hq f2).halt ?_
  have h := outerU_run (E := E) (orc := orc) (x := x) hsw _ 0 0 (zero_add _) (Nat.zero_le _)
  have e : (∃ u', 0 ≤ u' ∧ u' < 2 ^ (x.length + 2) ^ (2 * E) ∧
      InitO orc x ((x.length + 2) ^ E) u' ∧
      ∃ v < 2 ^ (x.length + 2) ^ (2 * E), AccO orc x ((x.length + 2) ^ E) v ∧
        Reach (2 ^ (x.length + 2) ^ (2 * E)) (Rel orc x ((x.length + 2) ^ E))
          ((x.length + 2) ^ (2 * E)) u' v) ↔
      ∃ u < 2 ^ (x.length + 2) ^ (2 * E), InitO orc x ((x.length + 2) ^ E) u ∧
        ∃ v < 2 ^ (x.length + 2) ^ (2 * E), AccO orc x ((x.length + 2) ^ E) v ∧
          Reach (2 ^ (x.length + 2) ^ (2 * E)) (Rel orc x ((x.length + 2) ^ E))
            ((x.length + 2) ^ (2 * E)) u v :=
    ⟨fun ⟨u, _, h1, h2⟩ => ⟨u, h1, h2⟩, fun ⟨u, h1, h2⟩ => ⟨u, Nat.zero_le _, h1, h2⟩⟩
  rw [decide_eq_decide.mpr e] at h
  exact h

end SavitchARM

end Complexity.LogProg
