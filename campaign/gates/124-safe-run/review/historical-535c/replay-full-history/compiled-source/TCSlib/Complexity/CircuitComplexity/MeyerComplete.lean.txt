/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.MeyerSoundInput

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Meyer's theorem: completeness of the checks

The true head-relative tableau of an accepting run passes every check of
`MeyerVerifier.lean` ([AB09, proof of Thm 6.20]: the circuit computing the true
transcript satisfies all local criteria). As for soundness, the argument is for a
numeric oracle (`Complexity.Meyer.complete_numeric`); here the oracle answers truthfully
on every in-range query.

## Main definitions

* `Complexity.Meyer.edgeOf` — the edge of a sign and a magnitude.

## Main results

* `Complexity.Meyer.complete_numeric` — the truthful oracle passes all checks when the
  run is accepting by time `2^W - 1`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§6.4, Theorem 6.20, pp. 114–115.)
-/

namespace Complexity.Meyer

open Turing Complexity.TimeHierarchy

variable {M : FinTM Bool} {Ans : Sel M → ℕ → ℕ → Bool} {W : ℕ} {x : List Bool}

/-- The edge of a sign and a magnitude. -/
def edgeOf (s : Bool) (a : ℕ) : ℤ := if s then -(a : ℤ) - 1 else a

/-- The edge of sign `s` has sign `s`. -/
theorem sE_edgeOf (s : Bool) (a : ℕ) : sE (edgeOf s a) = s := by
  cases s <;> simp [sE, edgeOf]; omega

/-- The edge of magnitude `a` has magnitude `a`. -/
theorem aE_edgeOf (s : Bool) (a : ℕ) : aE (edgeOf s a) = a := by
  cases s <;> simp [aE, edgeOf]; omega

section complete

variable (hT : ∀ sel t a, t < 2 ^ W → a < 2 ^ W →
  Ans sel t a = tabAns M sel (M.tm.runFrom (M.tm.initCfg x) t) a)

include hT

/-- A truthful oracle's work symbols are the true cells. -/
theorem sv_true_some (h : Fin M.k) (s : Bool) {t a : ℕ} (ht : t < 2 ^ W) (ha : a < 2 ^ W) :
    sv M Ans (some h) s t a = RW (M.tm.runFrom (M.tm.initCfg x) t) h (sgnZ s a) := by
  simp only [sv, hT _ t a ht ha, tabAns_sym_some, decode_symBit]

/-- A truthful oracle's input symbols are the true cells. -/
theorem sv_true_none (s : Bool) {t a : ℕ} (ht : t < 2 ^ W) (ha : a < 2 ^ W) :
    sv M Ans none s t a = RI (M.tm.runFrom (M.tm.initCfg x) t) (sgnZ s a) := by
  simp only [sv, hT _ t a ht ha, tabAns_sym_none, decode_symBit]

/-- A truthful oracle's state claims are the true state. -/
theorem st_true (σ : Option M.State × OutReg) {t : ℕ} (ht : t < 2 ^ W) :
    Ans (.st σ.1 σ.2) t 0 = decide (σ = SS (M.tm.runFrom (M.tm.initCfg x) t)) := by
  rw [hT _ t 0 ht (Nat.two_pow_pos W), tabAns_st]
  simp only [SS]
  by_cases h : σ = ((M.tm.runFrom (M.tm.initCfg x) t).state,
    OutReg.ofList (M.tm.runFrom (M.tm.initCfg x) t).output)
  · subst h; simp
  · rw [decide_eq_false h]
    rw [decide_eq_false]
    rintro ⟨h1, h2⟩
    exact h (Prod.ext h1.symm h2.symm)

/-- **A truthful oracle's claims are true**: claimed state and reads are the true ones. -/
theorem claims_true {t a j : ℕ} {b : Bool} (ht : t < 2 ^ W) (σ : Option M.State × OutReg)
    (ρ : Rd M) (hcl : claims M (NumVal M Ans W x.length t a j b) .tc σ ρ = true) :
    σ = SS (M.tm.runFrom (M.tm.initCfg x) t) ∧ ρ = reads (M.tm.runFrom (M.tm.initCfg x) t) := by
  have hpos := Nat.two_pow_pos W
  simp only [claims, stA_NumVal, symvA_NumVal, tvOf, avOf, Bool.and_eq_true,
    decide_eq_true_eq] at hcl
  obtain ⟨⟨h1, h2⟩, h3⟩ := hcl
  rw [st_true hT σ ht] at h1
  refine ⟨of_decide_eq_true h1, Prod.ext ?_ (funext fun h => ?_)⟩
  · rw [← h2, sv_true_none hT false ht hpos]; simp [reads, sgnZ]
  · rw [← h3 h, sv_true_some hT h false ht hpos]; simp [reads, sgnZ]

/-- **The work step check holds for the truthful oracle** on every edge in range.

**Proof sketch.** Rewrite the guessed cells of the edge as true cells (`sv_true_some`,
`edge_c1`, `edge_c2`); the claimed step is then the local work rule `RW_step` of the true
run, case by case on the head move. -/
theorem workOK_true {t j : ℕ} {b : Bool} (ht : t + 1 < 2 ^ W) (h : Fin M.k) (e : ℤ)
    (he : aE e + 1 < 2 ^ W) :
    workOK M (NumVal M Ans W x.length t (aE e) j b) (SS (M.tm.runFrom (M.tm.initCfg x) t))
      (reads (M.tm.runFrom (M.tm.initCfg x) t)) h (sE e) = true := by
  have s1 : ∀ T : TW, T = .tc ∨ T = .tn →
      sv M Ans (some h) (sE e) (tvOf W t T) (if sE e then aE e + 1 else aE e) =
        RW (M.tm.runFrom (M.tm.initCfg x) (tvOf W t T)) h e := by
    rintro T (rfl | rfl) <;>
    · rw [sv_true_some hT h _ (by simp [tvOf]; omega) (by split_ifs <;> omega), edge_c1]
  have s2 : ∀ T : TW, T = .tc ∨ T = .tn →
      sv M Ans (some h) (sE e) (tvOf W t T) (if sE e then aE e else aE e + 1) =
        RW (M.tm.runFrom (M.tm.initCfg x) (tvOf W t T)) h (e + 1) := by
    rintro T (rfl | rfl) <;>
    · rw [sv_true_some hT h _ (by simp [tvOf]; omega) (by split_ifs <;> omega), edge_c2]
  simp only [workOK, symvA_NumVal, avOf_ite]
  simp only [avOf, NumVal, edge_E0, edge_E1]
  rw [s1 .tc (Or.inl rfl), s1 .tn (Or.inr rfl), s2 .tc (Or.inl rfl), s2 .tn (Or.inr rfl)]
  simp only [tvOf, MultiTapeTM.runFrom_succ_eq_step', RW_step, SS]
  generalize M.tm.runFrom (M.tm.initCfg x) t = c
  unfold ruleW
  cases hq : c.state with
  | none => simp
  | some q =>
    simp only [decide_eq_true_eq]
    cases hm : ((M.tm.tr q (reads c).1 (reads c).2).workTapes h).2 with
    | zero => simp
    | pos => simp [SignType.pos_eq_one]
    | neg =>
      simp

/-- **The input step check holds for the truthful oracle** on every input edge.

**Proof sketch.** As `workOK_true`, with `RI_step`; the guessed clamping test reads the true
cell at offset `m`, so each branch is the corresponding branch of the true input rule. -/
theorem inOK_true {t a : ℕ} {b : Bool} (ht : t + 1 < 2 ^ W) (hn : x.length + 2 < 2 ^ W)
    (e : ℤ) (he1 : -((x.length : ℤ) + 1) ≤ e) (he2 : e ≤ x.length) :
    inOK M (NumVal M Ans W x.length t a (aE e) b) (SS (M.tm.runFrom (M.tm.initCfg x) t))
      (reads (M.tm.runFrom (M.tm.initCfg x) t)) (sE e) = true := by
  have hj : aE e ≤ x.length := by unfold aE; split_ifs <;> omega
  have s1 : ∀ T : TW, T = .tc ∨ T = .tn →
      sv M Ans none (sE e) (tvOf W t T) (if sE e then aE e + 1 else aE e) =
        RI (M.tm.runFrom (M.tm.initCfg x) (tvOf W t T)) e := by
    rintro T (rfl | rfl) <;>
    · rw [sv_true_none hT _ (by simp [tvOf]; omega) (by split_ifs <;> omega), edge_c1]
  have s2 : ∀ T : TW, T = .tc ∨ T = .tn →
      sv M Ans none (sE e) (tvOf W t T) (if sE e then aE e else aE e + 1) =
        RI (M.tm.runFrom (M.tm.initCfg x) (tvOf W t T)) (e + 1) := by
    rintro T (rfl | rfl) <;>
    · rw [sv_true_none hT _ (by simp [tvOf]; omega) (by split_ifs <;> omega), edge_c2]
  have hcl : ∀ m : SignType, m ≠ 0 →
      sv M Ans none (decide (m = .neg)) (tvOf W t .tc) 1 =
        RI (M.tm.runFrom (M.tm.initCfg x) t) (m : ℤ) := by
    intro m hm
    rw [sv_true_none hT _ (by simp [tvOf]; omega) (by omega)]
    cases m <;> simp [sgnZ, tvOf] at hm ⊢
  simp only [inOK, clampedA, symvA_NumVal, avOf_ite]
  simp only [avOf]
  rw [s1 .tc (Or.inl rfl), s1 .tn (Or.inr rfl), s2 .tc (Or.inl rfl), s2 .tn (Or.inr rfl)]
  simp only [tvOf] at hcl
  simp only [tvOf, MultiTapeTM.runFrom_succ_eq_step', RI_step, SS]
  generalize M.tm.runFrom (M.tm.initCfg x) t = c at hcl
  unfold ruleI
  cases hq : c.state with
  | none => simp
  | some q =>
    simp only
    have hcases : ∀ m : SignType, m = .zero ∨ m = .pos ∨ m = .neg := by decide
    rcases hcases (M.tm.tr q (reads c).1 (reads c).2).inputTape with hm | hm | hm <;>
      simp only [hm]
    · simp
    · have hp : sv M Ans none false t 1 = RI c 1 := by
        have := hcl .pos (by decide); simpa [SignType.pos_eq_one] using this
      simp only [SignType.pos_eq_one, SignType.coe_one]
      by_cases hc' : (reads c).1 = none ∧ RI c 1 = none
      · simp [hc', hp]
      · have h1 : (decide ((reads c).1 = none) && decide (RI c 1 = none)) = false := by
          simpa using hc'
        simp [h1, hc', hp]
    · have hp : sv M Ans none true t 1 = RI c (-1) := by
        have := hcl .neg (by decide); simpa [SignType.neg_eq_neg_one] using this
      simp only [decide_true, hp, SignType.neg_eq_neg_one, SignType.coe_neg_one]
      by_cases hc' : (reads c).1 = none ∧ RI c (-1) = none
      · simp [hc']
      · have h1 : (decide ((reads c).1 = none) && decide (RI c (-1) = none)) = false := by
          simpa using hc'
        simp [h1, hc']

/-- **The input boundary check holds for the truthful oracle.**

**Proof sketch.** An unclamped outward move makes the outermost cell `±(|x|+1)` take the old
cell `±(|x|+2)`, which is blank (`RI_far`). -/
theorem bdOK_true {t a : ℕ} {b : Bool} (ht : t + 1 < 2 ^ W) (hn : x.length + 2 < 2 ^ W) :
    bdOK M (NumVal M Ans W x.length t a (x.length + 1) b) (SS (M.tm.runFrom (M.tm.initCfg x) t))
      (reads (M.tm.runFrom (M.tm.initCfg x) t)) = true := by
  have hcl : ∀ m : SignType, m ≠ 0 →
      sv M Ans none (decide (m = .neg)) (tvOf W t .tc) 1 =
        RI (M.tm.runFrom (M.tm.initCfg x) t) (m : ℤ) := by
    intro m hm
    rw [sv_true_none hT _ (by simp [tvOf]; omega) (by omega)]
    cases m <;> simp [sgnZ, tvOf] at hm ⊢
  have hfar : ∀ s : Bool, sv M Ans none s (tvOf W t .tn) (avOf a (x.length + 1) .aj) =
      RI (M.tm.runFrom (M.tm.initCfg x) (t + 1)) (sgnZ s (x.length + 1)) := by
    intro s
    rw [sv_true_none hT _ (by simp [tvOf]; omega) (by simp [avOf]; omega)]
    rfl
  simp only [bdOK, clampedA, symvA_NumVal, hfar]
  simp only [tvOf, avOf] at hcl ⊢
  simp only [MultiTapeTM.runFrom_succ_eq_step', RI_step, SS]
  generalize M.tm.runFrom (M.tm.initCfg x) t = c at hcl
  unfold ruleI
  cases hq : c.state with
  | none => rfl
  | some q =>
    simp only
    have hcases : ∀ m : SignType, m = .zero ∨ m = .pos ∨ m = .neg := by decide
    rcases hcases (M.tm.tr q (reads c).1 (reads c).2).inputTape with hm | hm | hm <;>
      simp only [hm]
    · have hp : sv M Ans none false t 1 = RI c 1 := by
        have := hcl .pos (by decide); simpa [SignType.pos_eq_one] using this
      by_cases hc' : (reads c).1 = none ∧ RI c 1 = none
      · simp [hc', hp, SignType.pos_eq_one]
      · simp only [SignType.pos_eq_one, SignType.coe_one, if_neg hc', sgnZ]
        rw [RI_far c _ (by simp; omega)]
        simp
    · have hp : sv M Ans none true t 1 = RI c (-1) := by
        have := hcl .neg (by decide); simpa [SignType.neg_eq_neg_one] using this
      by_cases hc' : (reads c).1 = none ∧ RI c (-1) = none
      · simp [hc', hp, SignType.neg_eq_neg_one]
      · simp only [SignType.neg_eq_neg_one, SignType.coe_neg_one, hp, if_neg hc', sgnZ, decide_true]
        simp only [decide_eq_true_eq, Bool.or_eq_true, ↓reduceIte]
        right
        exact RI_far c _ (by omega)

omit hT in
/-- The guessed initial input cell of a sign and a unary offset is the padded input.

**Proof sketch.** Case on the sign: the nonnegative side reads `x[j]?`, the negative side
(for `j ≠ 0`) lies left of the input and is blank. -/
theorem xin_sj {xb : ℕ → Bool} (hxb : ∀ j (hj : j < x.length), xb j = x[j]) (s : Bool) (j : ℕ) :
    (if (s && !decide (j = 0)) = true then none else if j < x.length then some (xb j) else none) =
      xhat x (1 + sgnZ s j) := by
  unfold xhat sgnZ
  cases s
  · simp only [Bool.false_and, Bool.false_eq_true, if_false, show (1 : ℤ) ≤ 1 + j by omega,
      if_true, show (1 + (j : ℤ) - 1).toNat = j by omega]
    by_cases hj : j < x.length
    · simp [hj, hxb _ hj]
    · simp [hj]
  · rcases Nat.eq_zero_or_pos j with rfl | hj
    · by_cases h0 : 0 < x.length
      · simp [h0, hxb _ h0]
      · simp [h0]
    · have : j ≠ 0 := by omega
      simp only [this, decide_false, Bool.not_false, Bool.true_and, if_true]
      rw [if_neg (by omega)]

/-- **Completeness of the checks** [AB09, proof of Thm 6.20]: if the oracle answers every
in-range query truthfully and the run of `M` on `x` is halted with output `[true]` by time
`2^W - 1`, then every check passes on every instance.

**Proof sketch.** The initial-row checks are the initial configuration (`SS_init`,
`RW_init`, `RI_init`); a passing claim is the true state and reads (`claims_true`), so
the step checks are the local rules of the run (`SS_step`, `workOK_true`, `inOK_true`,
`bdOK_true`); the final check is the acceptance hypothesis. -/
theorem complete_numeric {xb : ℕ → Bool} (hxb : ∀ j (hj : j < x.length), xb j = x[j])
    (hn : x.length + 2 < 2 ^ W)
    (hacc : SS (M.tm.runFrom (M.tm.initCfg x) (2 ^ W - 1)) = (none, OutReg.one true)) :
    AllGood M Ans (W := W) (x := x) xb := by
  have hpos := Nat.two_pow_pos W
  intro t a j ht ha hj π
  cases π with
  | initSt σ r =>
    simp only [goodF, NumVal_ans, tvOf, avOf, beq_iff_eq]
    rw [st_true hT (σ, r) hpos, MultiTapeTM.runFrom_zero, SS_init]
  | initW h s b =>
    simp only [goodF, NumVal_ans, tvOf, avOf, beq_iff_eq]
    rw [hT _ 0 a hpos ha, tabAns_sym_some, MultiTapeTM.runFrom_zero, RW_init]
  | initI s b =>
    simp only [goodF, tvOf, avOf, beq_iff_eq, xinV, NumVal, decide_eq_true_eq]
    rw [hT _ 0 j hpos (by omega), tabAns_sym_none, MultiTapeTM.runFrom_zero, RI_init,
      xin_sj hxb s j]
  | negZero τ b =>
    simp only [goodF, NumVal_ans, tvOf, avOf, beq_iff_eq]
    rw [hT _ t 0 ht hpos, hT _ t 0 ht hpos]
    cases τ with
    | none => simp [tabAns_sym_none, sgnZ]
    | some h => simp [tabAns_sym_some, sgnZ]
  | stepSt σ ρ σ' =>
    simp only [goodF, NumVal]
    by_cases hg : t + 1 < 2 ^ W ∧ claims M (NumVal M Ans W x.length t a j (xb j)) .tc σ ρ = true
    · obtain ⟨ht1, hcl⟩ := hg
      obtain ⟨rfl, rfl⟩ := claims_true hT ht σ ρ hcl
      simp only [ht1, decide_true, hcl, Bool.and_self, Bool.not_true, Bool.false_or,
        tvOf, avOf, beq_iff_eq]
      rw [st_true hT σ' ht1, MultiTapeTM.runFrom_succ_eq_step', SS_step]
    · simp only [not_and] at hg
      by_cases ht1 : t + 1 < 2 ^ W
      · simp [ht1, hg ht1]
      · simp [ht1]
  | stepW σ ρ h s =>
    simp only [goodF, NumVal]
    by_cases hg : t + 1 < 2 ^ W ∧ a + 1 < 2 ^ W ∧
        claims M (NumVal M Ans W x.length t a j (xb j)) .tc σ ρ = true
    · obtain ⟨ht1, ha1, hcl⟩ := hg
      obtain ⟨rfl, rfl⟩ := claims_true hT ht σ ρ hcl
      simp only [ht1, ha1, decide_true, hcl, Bool.and_self, Bool.not_true, Bool.false_or]
      obtain ⟨e, rfl, rfl⟩ : ∃ e, sE e = s ∧ aE e = a :=
        ⟨edgeOf s a, sE_edgeOf s a, aE_edgeOf s a⟩
      exact workOK_true hT ht1 h e ha1
    · by_cases ht1 : t + 1 < 2 ^ W
      · by_cases ha1 : a + 1 < 2 ^ W
        · have : claims M (NumVal M Ans W x.length t a j (xb j)) .tc σ ρ = false := by
            simpa [ht1, ha1] using hg
          simp [this]
        · simp [ha1]
      · simp [ht1]
  | stepI σ ρ s =>
    simp only [goodF, NumVal]
    by_cases hg : t + 1 < 2 ^ W ∧ j ≤ x.length ∧
        claims M (NumVal M Ans W x.length t a j (xb j)) .tc σ ρ = true
    · obtain ⟨ht1, hj1, hcl⟩ := hg
      obtain ⟨rfl, rfl⟩ := claims_true hT ht σ ρ hcl
      simp only [ht1, hj1, decide_true, hcl, Bool.and_self, Bool.not_true, Bool.false_or]
      obtain ⟨e, rfl, rfl⟩ : ∃ e, sE e = s ∧ aE e = j :=
        ⟨edgeOf s j, sE_edgeOf s j, aE_edgeOf s j⟩
      exact inOK_true hT ht1 hn e (by unfold aE at hj1; split_ifs at hj1 <;> omega)
        (by unfold aE at hj1; split_ifs at hj1 <;> omega)
    · by_cases ht1 : t + 1 < 2 ^ W
      · by_cases hj1 : j ≤ x.length
        · have : claims M (NumVal M Ans W x.length t a j (xb j)) .tc σ ρ = false := by
            simpa [ht1, hj1] using hg
          simp [this]
        · simp [hj1]
      · simp [ht1]
  | bdryI σ ρ =>
    simp only [goodF, NumVal]
    by_cases hg : t + 1 < 2 ^ W ∧ j = x.length + 1 ∧
        claims M (NumVal M Ans W x.length t a j (xb j)) .tc σ ρ = true
    · obtain ⟨ht1, rfl, hcl⟩ := hg
      obtain ⟨rfl, rfl⟩ := claims_true hT ht σ ρ hcl
      simp only [ht1, decide_true, hcl, Bool.and_self, Bool.not_true, Bool.false_or]
      exact bdOK_true hT ht1 hn
    · by_cases ht1 : t + 1 < 2 ^ W
      · by_cases hj1 : j = x.length + 1
        · have : claims M (NumVal M Ans W x.length t a j (xb j)) .tc σ ρ = false := by
            simpa [ht1, hj1] using hg
          simp [this]
        · simp [hj1]
      · simp [ht1]
  | final =>
    simp only [goodF, NumVal_ans, tvOf, avOf]
    rw [st_true hT (none, OutReg.one true) (by omega), hacc]
    simp

end complete

end Complexity.Meyer
