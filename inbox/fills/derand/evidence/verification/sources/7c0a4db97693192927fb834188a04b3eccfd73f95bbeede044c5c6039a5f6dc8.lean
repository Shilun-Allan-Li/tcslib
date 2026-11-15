/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.ExpBFS.Relax
import Mathlib.Algebra.BigOperators.Intervals

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The breadth-first search of the search machine

Run lemmas for one search of `Complexity.LogProg.ExpBFS.A` over the codes `u < K`, its marks
kept at the memory cells `Bs + u`, after the initial marking and the relaxation round of
`TCSlib.Complexity.SpaceComplexity.ExpBFS.Relax`: the rounds until nothing changes
(`rounds_run`, by induction on the number of unmarked codes), the count (`count_run`), and the
whole search (`search_run`): it ends with the marks at `Bs + v` exactly at the codes `v < K`
reachable from an initial code `u < K` through step pairs below `K`, and with their number
in `c`.

Infrastructure for [AB09, §4.1.1, proof of Theorem 4.2]; not itself a result of the book.

## Main definitions

* `Complexity.LogProg.ExpBFS.unmarked` — the number of unmarked codes of the region.

## Main results

* `Complexity.LogProg.ExpBFS.rounds_run`, `Complexity.LogProg.ExpBFS.count_run`.
* `Complexity.LogProg.ExpBFS.search_run` — a search marks exactly the reachable codes and
  counts them.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1, Theorem 4.2.)
-/

namespace Complexity.LogProg

namespace ExpBFS

open Turing

variable {K₀ : ℕ} {orc : Fin 4 → List Bool → Bool} {x : List Bool} {B P : ℕ}

/-! ## The rounds -/

/-- The number of unmarked codes of the region. -/
noncomputable def unmarked (b K : ℕ) (M : ℤ → Bool) : ℕ :=
  ((Finset.range K).filter fun v => M (cell b v) = false).card

/-- A memory that grew, only in the region, and changed, has fewer unmarked codes.

**Proof sketch.** Some cell changed; by `Out` it is a region cell `Bs + v`, by `Mono` it
changed from `0` to `1`. The unmarked codes afterwards are a proper subset of those before. -/
lemma unmarked_lt {b K : ℕ} {M M' : ℤ → Bool} (hm : Mono M M') (ho : Out b K M M')
    (hne : M' ≠ M) : unmarked b K M' < unmarked b K M := by
  classical
  obtain ⟨z, hz⟩ : ∃ z, M' z ≠ M z := by
    by_contra h; push_neg at h; exact hne (funext h)
  have hin : ∃ v, v < K ∧ z = cell b v := by
    by_contra h; push_neg at h; exact hz (ho z fun v hv e => h v hv e)
  obtain ⟨v, hv, rfl⟩ := hin
  have hMv : M (cell b v) = false := by
    cases h : M (cell b v)
    · rfl
    · exact absurd (hm _ h) (by rw [h] at hz; simpa using hz)
  apply Finset.card_lt_card
  refine ⟨fun w hw => ?_, fun h => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_range] at hw ⊢
    refine ⟨hw.1, ?_⟩
    cases h : M (cell b w)
    · rfl
    · rw [hm _ h] at hw; exact absurd hw.2 (by simp)
  · have := h (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hv, hMv⟩)
    simp only [Finset.mem_filter, Finset.mem_range] at this
    have h' : M' (cell b v) = true := by
      cases h'' : M' (cell b v)
      · rw [h'', hMv] at hz; exact absurd rfl hz
      · rfl
    rw [h'] at this; exact absurd this.2 (by simp)

/-- **The rounds**: from `rl0` with `U = K` and `V` clear, the machine repeats relaxation
rounds until one marks nothing, and reaches `cn0` with the change flag clear. The final marks
contain the old ones, are closed under step pairs below `K`, and stay inside any set closed
under step pairs that contains the old marks.

**Proof sketch.** Strong induction on the number of unmarked codes (`unmarked_lt`); each round
is `outer_run` from `U = 0`, the change flag cleared. -/
theorem rounds_run (φ : Bool) : ∀ (j : ℕ) (S : St) (M : ℤ → Bool), unmarked S.Bs S.K M = j →
    S.U = S.K → S.V = 0 → S.T = 0 → S.T2 = 0 → S.Z = 0 → S.ch ≤ 1 → SBd B P S →
    ∃ M', MReach (A K₀) orc x (G x B P) (cf (.rl0 φ) S M 0) (cf (.cn0 φ) { S with ch := 0 } M' 0) ∧
      Mono M M' ∧ Out S.Bs S.K M M' ∧
      (∀ Q : ℕ → Prop, (∀ a b, Q a → a < S.K → b < S.K →
          stp orc x (rr S φ) a b = true → Q b) →
        (∀ v, v < S.K → M (cell S.Bs v) = true → Q v) →
        ∀ v, v < S.K → M' (cell S.Bs v) = true → Q v) ∧
      (∀ a b, a < S.K → b < S.K → M' (cell S.Bs a) = true → stp orc x (rr S φ) a b = true →
        M' (cell S.Bs b) = true) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro S M hj hU hV hT hT2 hZ hch hS
  obtain ⟨hbd, hB1, hP1, hK1⟩ := hS
  have hbd0 : St.Bd B { S with U := 0 } := by simp only [St.Bd] at hbd ⊢; omega
  have hbd00 : St.Bd B { S with U := 0, ch := 0 } := by simp only [St.Bd] at hbd ⊢; omega
  refine ex1_pre (b := ?b6) ?p6 ?q6
  case p6 =>
    refine step_of rfl hbd ⟨le_rfl, by omega⟩ ?_
    simp only [astep]; regs
    refine step_of rfl hbd0 ⟨le_rfl, by omega⟩ ?_
    simp only [astep]; regs
    exact MReach.refl _
  obtain ⟨M1, c1, hr1, hm1, ho1, hc1, hq1, hcl1, he1, hn1⟩ :=
    outer_run (orc := orc) (x := x) (B := B) (P := P) (K₀ := K₀) φ (S.K - 0)
      { S with U := 0, ch := 0 } M rfl (by simp only; omega) hV hT hT2 hZ (by simp only; omega)
      ⟨hbd00, hB1, hP1, hK1⟩
  have hrr : rr { S with U := 0, ch := 0 } φ = rr S φ := by cases φ <;> rfl
  rw [hrr] at hq1 hcl1
  simp only at he1 hn1 hr1 hq1 hcl1 ho1
  refine ex1_pre (cont (st' := { S with U := 0, ch := 0 }) (by ext <;> simp) hr1) ?_
  have hbd1 : St.Bd B { S with U := S.K, ch := c1 } := by simp only [St.Bd] at hbd ⊢; omega
  refine ex1_pre (b := ?b7) ?p7 ?q7
  case p7 =>
    refine cont (st' := { S with U := S.K, ch := c1 }) (by ext <;> simp) ?_
    refine step_of rfl hbd1 ⟨le_rfl, by omega⟩ ?_
    simp only [astep]; regs
    exact MReach.refl _
  by_cases e : M1 = M
  · have hc0 : c1 = 0 := he1 e
    simp only [hc0, ↓reduceIte]
    subst e
    refine ⟨M1, ?_, Mono.refl _, Out.refl _ _ _, fun Q _ h => h, fun a b ha hb hMa hs => ?_⟩
    · refine reach_cf (MReach.refl _) ?_ rfl
      ext <;> simp [hU]
    · exact hcl1 rfl a b (Nat.zero_le _) ha hb hMa hs
  · have hc1' : c1 = 1 := hn1 e
    simp only [hc1', one_ne_zero, ↓reduceIte]
    obtain ⟨M', hr, hm, ho, hq, hcl⟩ := ih (unmarked S.Bs S.K M1)
      (hj ▸ unmarked_lt hm1 ho1 e) { S with U := S.K, ch := 1 } M1 rfl (by simp only)
      hV hT hT2 hZ (by simp only; omega)
      ⟨by simp only [St.Bd] at hbd ⊢; omega, hB1, hP1, hK1⟩
    have hrr2 : rr { S with U := S.K, ch := 1 } φ = rr S φ := by cases φ <;> rfl
    rw [hrr2] at hq hcl
    refine ⟨M', ?_, hm1.trans hm, ho1.trans ho, fun Q hQ hM => hq Q hQ (hq1 Q hQ hM), hcl⟩
    refine cont (st' := { S with U := S.K, ch := 1 }) (by ext <;> simp) ?_
    exact reach_cf hr (by ext <;> simp [hU]) rfl

/-! ## The count -/

/-- Splitting off the first code of a range. -/
lemma card_filter_Ico_succ {p : ℕ → Prop} [DecidablePred p] {u K : ℕ} (h : u < K) :
    ((Finset.Ico u K).filter p).card =
      (if p u then 1 else 0) + ((Finset.Ico (u + 1) K).filter p).card := by
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_eq_sum_Ico_succ_bot h]

/-- **The count**: from `cnU` with `U = u₀`, the machine adds to `c` the number of marked codes
`u₀ ≤ v < K` and reaches the search's exit with `U = K`.

**Proof sketch.** Induction on `K - U`: read the mark of `U` (`ac_run`), increment `c` if
marked, increment `U`. -/
theorem count_run (φ : Bool) : ∀ (j : ℕ) (S : St) (M : ℤ → Bool), S.K - S.U = j →
    S.U ≤ S.K → S.T = 0 → S.T2 = 0 → S.Z = 0 → S.c + (S.K - S.U) ≤ S.K → SBd B P S →
    MReach (A K₀) orc x (G x B P) (cf (.cnU φ) S M 0)
      (cf (if φ then .d2 else .d1 0)
        { S with U := S.K,
                 c := S.c + ((Finset.Ico S.U S.K).filter fun v => M (cell S.Bs v) = true).card }
        M 0) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro S M hj hUK hT hT2 hZ hc hS
  obtain ⟨hbd, hB1, hP1, hK1⟩ := hS
  by_cases hU : S.U = S.K
  · refine step_of rfl hbd ⟨le_rfl, by omega⟩ ?_
    simp only [astep]; regs [hU, ↓reduceIte]
    refine reach_cf (MReach.refl _) ?_ rfl
    ext <;> simp [hU]
  · have hlt : S.U < S.K := by omega
    refine step_of rfl hbd ⟨le_rfl, by omega⟩ ?_
    simp only [astep]; regs; rw [if_neg hU]
    have hac := ac_run (orc := orc) (x := x) (B := B) (P := P) (K₀ := K₀) (.cU φ) S M hbd hT
      hT2 hZ (by simp [Site.idx]; omega) (by simp [Site.idx]; omega)
    simp only [Site.set, Site.idx, St.toV_U, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
      acExit] at hac
    refine hac.trans ?_
    rw [card_filter_Ico_succ hlt]
    by_cases hb : M (cell S.Bs S.U) = true
    · simp only [hb, ↓reduceIte]
      have hbd1 : St.Bd B { S with c := S.c + 1 } := by simp only [St.Bd] at hbd ⊢; omega
      have hbd2 : St.Bd B { S with U := S.U + 1, c := S.c + 1 } := by
        simp only [St.Bd] at hbd ⊢; omega
      refine step_of rfl hbd ⟨le_rfl, by omega⟩ ?_
      simp only [astep]; regs
      refine step_of rfl hbd1 ⟨le_rfl, by omega⟩ ?_
      simp only [astep]; regs
      exact reach_cf (ih (S.K - (S.U + 1)) (by omega) { S with U := S.U + 1, c := S.c + 1 } M
        rfl (by simp only; omega) hT hT2 hZ (by simp only; omega) ⟨hbd2, hB1, hP1, hK1⟩)
        (by ext <;> simp; omega) rfl
    · rw [Bool.not_eq_true] at hb
      simp only [hb, Bool.false_eq_true, ↓reduceIte, zero_add]
      have hbd1 : St.Bd B { S with U := S.U + 1 } := by simp only [St.Bd] at hbd ⊢; omega
      refine step_of rfl hbd ⟨le_rfl, by omega⟩ ?_
      simp only [astep]; regs
      exact reach_cf (ih (S.K - (S.U + 1)) (by omega) { S with U := S.U + 1 } M rfl
        (by simp only; omega) hT hT2 hZ (by simp only; omega) ⟨hbd1, hB1, hP1, hK1⟩)
        (by ext <;> simp) rfl

/-! ## The search -/

open Classical in
/-- **A search**: from `iU` with `U`, `V`, the change flag, `c`, `T`, `T2`, `Z` clear and the
region `[Bs, Bs + K)` unmarked, the machine reaches the search's exit with `U = K`, the marks
at `Bs + v` exactly at the reachable codes `v < K` (`Cl`), their number in `c`, and the memory
outside the region unchanged.

**Proof sketch.** `ini_run` marks the initial codes, which are reachable; `rounds_run` closes
the marks under step pairs while keeping them reachable; reachable codes are marked by
induction along their paths; `count_run` counts the marks. -/
theorem search_run (φ : Bool) (S : St) (M : ℤ → Bool) (hU : S.U = 0) (hV : S.V = 0)
    (hT : S.T = 0) (hT2 : S.T2 = 0) (hZ : S.Z = 0) (hch : S.ch = 0) (hc : S.c = 0)
    (hS : SBd B P S) (hfresh : ∀ v, v < S.K → M (cell S.Bs v) = false) :
    ∃ M', MReach (A K₀) orc x (G x B P) (cf (.iU φ) S M 0)
        (cf (if φ then .d2 else .d1 0)
          { S with U := S.K, c := ((Finset.range S.K).filter (Cl orc x (rr S φ) S.K)).card }
          M' 0) ∧
      Mono M M' ∧ Out S.Bs S.K M M' ∧
      ∀ v, v < S.K → (M' (cell S.Bs v) = true ↔ Cl orc x (rr S φ) S.K v) := by
  classical
  obtain ⟨hbd, hB1, hP1, hK1⟩ := hS
  obtain ⟨M1, hr1, hm1, ho1, hmk1, hcl1⟩ := ini_run (orc := orc) (x := x) (B := B) (P := P)
    (K₀ := K₀) φ (S.K - S.U) S M rfl (by omega) hT hT2 hZ ⟨hbd, hB1, hP1, hK1⟩
  have hbdK : St.Bd B { S with U := S.K } := by simp only [St.Bd] at hbd ⊢; omega
  obtain ⟨M2, hr2, hm2, ho2, hq2, hcl2⟩ := rounds_run (orc := orc) (x := x) (B := B) (P := P)
    (K₀ := K₀) φ _ { S with U := S.K } M1 rfl rfl hV hT hT2 hZ (by simp only; omega)
    ⟨hbdK, hB1, hP1, hK1⟩
  have hrr : rr { S with U := S.K } φ = rr S φ := by cases φ <;> rfl
  rw [hrr] at hq2 hcl2
  simp only at hq2 hcl2 ho2 hr2
  -- the marks are the reachable codes
  have hinv : ∀ v, v < S.K → M2 (cell S.Bs v) = true → Cl orc x (rr S φ) S.K v := by
    refine hq2 (Cl orc x (rr S φ) S.K) (fun a b ha _ hb hs => ha.step hs hb) ?_
    intro v hv h
    rcases hcl1 v hv h with h' | h'
    · rw [hfresh v hv] at h'; cases h'
    · exact ⟨v, hv, h', Relation.ReflTransGen.refl⟩
  have hcov : ∀ v, Cl orc x (rr S φ) S.K v → M2 (cell S.Bs v) = true := by
    rintro v ⟨u, hu, hi, hpath⟩
    have hmarked : ∀ w, Relation.ReflTransGen (fun a b => stp orc x (rr S φ) a b = true ∧
        b < S.K) u w → w < S.K ∧ M2 (cell S.Bs w) = true := by
      intro w hw
      induction hw with
      | refl => exact ⟨hu, hm2 _ (hmk1 u (by omega) hu hi)⟩
      | tail _ hst ih => exact ⟨hst.2, hcl2 _ _ ih.1 hst.2 ih.2 hst.1⟩
    exact (hmarked v hpath).2
  have hiff : ∀ v, v < S.K → (M2 (cell S.Bs v) = true ↔ Cl orc x (rr S φ) S.K v) :=
    fun v hv => ⟨hinv v hv, hcov v⟩
  refine ⟨M2, ?_, hm1.trans hm2, ho1.trans ho2, hiff⟩
  refine (hr1.trans hr2).trans ?_
  have hbdK0 : St.Bd B { S with U := S.K, ch := 0 } := by simp only [St.Bd] at hbd ⊢; omega
  refine step_of rfl hbdK0 ⟨le_rfl, by omega⟩ ?_
  simp only [astep]; regs
  have hcnt := count_run (orc := orc) (x := x) (B := B) (P := P) (K₀ := K₀) φ (S.K - 0)
    { S with U := 0, ch := 0 } M2 (by simp) (by simp) hT hT2 hZ (by simp [hc])
    ⟨by simp only [St.Bd] at hbd ⊢; omega, hB1, hP1, hK1⟩
  have hceq : ((Finset.range S.K).filter fun v : ℕ => M2 ((S.Bs : ℤ) + (v : ℤ)) = true).card =
      ((Finset.range S.K).filter (Cl orc x (rr S φ) S.K)).card := by
    refine congrArg Finset.card (Finset.filter_congr fun v hv => ?_)
    have := hiff v (Finset.mem_range.mp hv)
    simpa [cell] using this
  refine reach_cf hcnt ?_ rfl
  ext <;> simp [hc, hch, hceq]

end ExpBFS

end Complexity.LogProg
