/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.MeyerSound

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Meyer's theorem: soundness of the checks, input tape and induction

The input-tape half of the step of the soundness induction (`in_edge`, `bd_edge`,
`input_correct`), the induction over time (`correct_all`), and the final soundness
statement `Complexity.Meyer.sound_numeric` ([AB09, proof of Thm 6.20]: the transcript
implicitly computed by a circuit passing all local checks is the true one).

## Main definitions

None; the numeric valuation and guessed cells are those of `MeyerSound.lean`.

## Main results

* `Complexity.Meyer.input_correct` — correct rows stay correct on the input tape.
* `Complexity.Meyer.correct_all` — every guessed row is correct.
* `Complexity.Meyer.sound_numeric` — checks passed on all instances force the final row
  of the true run to be halted with output summary `one true`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§6.4, Theorem 6.20, pp. 114–115.)
-/

namespace Complexity.Meyer

open Turing Complexity.TimeHierarchy

variable {M : FinTM Bool} {Ans : Sel M → ℕ → ℕ → Bool}

section sound

variable {W : ℕ} {x : List Bool} {xb : ℕ → Bool}

/-- The guessed clamping test reads the guessed cell at offset `m`. -/
theorem clamp_cX (H : AllGood M Ans (W := W) (x := x) xb) {t : ℕ} (ht : t < 2 ^ W)
    (m : SignType) (hm : m ≠ 0) :
    sv M Ans none (decide (m = .neg)) t 1 = cX M Ans none t (m : ℤ) := by
  rw [sv_sgn H none t ht]
  congr 1
  cases m <;> simp [sgnZ] at hm ⊢

/-- **The input edge facts**: the step check on the input edge `(e, e + 1)` at a correct
row `t`, for `-(|x|+1) ≤ e ≤ |x|`.

**Proof sketch.** Instantiate the input-step check at the unary edge `(sE e, aE e)` with the
true claims; translate its cells to signed offsets and the guessed clamping test to the cell
at offset `m` (`clamp_cX`). -/
theorem in_edge (H : AllGood M Ans (W := W) (x := x) xb) {t : ℕ} (ht : t + 1 < 2 ^ W)
    (hc : Correct M Ans W x t) (e : ℤ)
    (he1 : -((x.length : ℤ) + 1) ≤ e) (he2 : e ≤ x.length) :
    let c := M.tm.runFrom (M.tm.initCfg x) t
    let same := cX M Ans none (t + 1) e = cX M Ans none t e ∧
      cX M Ans none (t + 1) (e + 1) = cX M Ans none t (e + 1)
    match c.state with
    | none => same
    | some q =>
      let m := (M.tm.tr q (reads c).1 (reads c).2).inputTape
      let cl := (reads c).1 = none ∧ cX M Ans none t (m : ℤ) = none
      match m with
      | .zero => same
      | .pos => if cl then same else cX M Ans none (t + 1) e = cX M Ans none t (e + 1)
      | .neg => if cl then same else cX M Ans none (t + 1) (e + 1) = cX M Ans none t e := by
  intro c same
  have hj : aE e ≤ x.length := by unfold aE; split_ifs <;> omega
  have hg := H t 0 (aE e) (by omega) (Nat.two_pow_pos W) (by omega)
    (.stepI (SS c) (reads c) (sE e))
  have hcl := claims_of_correct hc (by omega) 0 (aE e) (xb (aE e))
  simp only [goodF] at hg
  rw [hcl] at hg
  simp only [NumVal, ht, decide_true, hj, Bool.true_and, Bool.not_true, Bool.false_or] at hg
  have s1 : ∀ T, sv M Ans none (sE e) (tvOf W t T) (if sE e then aE e + 1 else aE e) =
      cX M Ans none (tvOf W t T) e := by
    intro T
    rw [sv_sgn H _ _ ?_ _ _, edge_c1]
    cases T <;> simp [tvOf] <;> omega
  have s2 : ∀ T, sv M Ans none (sE e) (tvOf W t T) (if sE e then aE e else aE e + 1) =
      cX M Ans none (tvOf W t T) (e + 1) := by
    intro T
    rw [sv_sgn H _ _ ?_ _ _, edge_c2]
    cases T <;> simp [tvOf] <;> omega
  simp only [inOK, clampedA, symvA_NumVal, avOf_ite] at hg
  simp only [avOf] at hg
  have hsc : (SS c).1 = c.state := rfl
  rw [hsc] at hg
  have hsame : ((decide (sv M Ans none (sE e) (tvOf W t .tn) (if sE e then aE e + 1 else aE e) =
        sv M Ans none (sE e) (tvOf W t .tc) (if sE e then aE e + 1 else aE e))) &&
      decide (sv M Ans none (sE e) (tvOf W t .tn) (if sE e then aE e else aE e + 1) =
        sv M Ans none (sE e) (tvOf W t .tc) (if sE e then aE e else aE e + 1))) = true ↔ same := by
    rw [s1, s1, s2, s2]; simp [same, tvOf]
  cases hq : c.state with
  | none =>
    simp only [hq] at hg
    exact hsame.mp hg
  | some q =>
    simp only [hq] at hg ⊢
    cases hm : (M.tm.tr q (reads c).1 (reads c).2).inputTape with
    | zero =>
      simp only [hm] at hg
      exact hsame.mp hg
    | pos =>
      simp only [hm] at hg ⊢
      have hc1 : sv M Ans none false (tvOf W t .tc) 1 = cX M Ans none t ((SignType.pos : SignType) : ℤ) := by
        rw [sv_sgn H none _ (by simp [tvOf]; omega)]; simp [sgnZ, tvOf]
      simp only [show (SignType.pos = SignType.neg) = False from by simp, decide_false] at hg
      rw [hc1] at hg
      by_cases hcl' : (reads c).1 = none ∧ cX M Ans none t ((SignType.pos : SignType) : ℤ) = none
      · rw [if_pos hcl']
        rw [show (decide ((reads c).1 = none) && decide (cX M Ans none t
          ((SignType.pos : SignType) : ℤ) = none)) = true by simpa using hcl'] at hg
        exact hsame.mp (by simpa using hg)
      · rw [if_neg hcl']
        rw [show (decide ((reads c).1 = none) && decide (cX M Ans none t
          ((SignType.pos : SignType) : ℤ) = none)) = false by simpa using hcl'] at hg
        simp only [Bool.false_eq_true, if_false, decide_eq_true_eq] at hg
        rw [s1 .tn, s2 .tc] at hg
        simpa [tvOf] using hg
    | neg =>
      simp only [hm] at hg ⊢
      have hc1 : sv M Ans none true (tvOf W t .tc) 1 = cX M Ans none t ((SignType.neg : SignType) : ℤ) := by
        rw [sv_sgn H none _ (by simp [tvOf]; omega)]; simp [sgnZ, tvOf, SignType.neg_eq_neg_one]
      simp only [decide_true] at hg
      rw [hc1] at hg
      by_cases hcl' : (reads c).1 = none ∧ cX M Ans none t ((SignType.neg : SignType) : ℤ) = none
      · rw [if_pos hcl']
        rw [show (decide ((reads c).1 = none) && decide (cX M Ans none t
          ((SignType.neg : SignType) : ℤ) = none)) = true by simpa using hcl'] at hg
        exact hsame.mp (by simpa using hg)
      · rw [if_neg hcl']
        rw [show (decide ((reads c).1 = none) && decide (cX M Ans none t
          ((SignType.neg : SignType) : ℤ) = none)) = false by simpa using hcl'] at hg
        simp only [Bool.false_eq_true, if_false, decide_eq_true_eq] at hg
        rw [s2 .tn, s1 .tc] at hg
        simpa [tvOf] using hg

/-- **The input boundary facts**: an unclamped outward move blanks the outermost guessed
input cell.

**Proof sketch.** Instantiate the boundary check at `j = |x| + 1` with the true claims and
translate its cells to the offsets `±(|x|+1)`. -/
theorem bd_edge (H : AllGood M Ans (W := W) (x := x) xb) {t : ℕ} (ht : t + 1 < 2 ^ W)
    (hc : Correct M Ans W x t) :
    let c := M.tm.runFrom (M.tm.initCfg x) t
    match c.state with
    | none => True
    | some q =>
      let m := (M.tm.tr q (reads c).1 (reads c).2).inputTape
      let cl := (reads c).1 = none ∧ cX M Ans none t (m : ℤ) = none
      match m with
      | .zero => True
      | .pos => cl ∨ cX M Ans none (t + 1) ((x.length : ℤ) + 1) = none
      | .neg => cl ∨ cX M Ans none (t + 1) (-((x.length : ℤ) + 1)) = none := by
  intro c
  have hg := H t 0 (x.length + 1) (by omega) (Nat.two_pow_pos W) le_rfl (.bdryI (SS c) (reads c))
  have hcl := claims_of_correct hc (by omega) 0 (x.length + 1) (xb (x.length + 1))
  simp only [goodF] at hg
  rw [hcl] at hg
  simp only [NumVal, ht, decide_true, Bool.true_and, Bool.not_true, Bool.false_or] at hg
  simp only [bdOK, clampedA, symvA_NumVal] at hg
  have hsc : (SS c).1 = c.state := rfl
  rw [hsc] at hg
  cases hq : c.state with
  | none => trivial
  | some q =>
    simp only [hq] at hg ⊢
    cases hm : (M.tm.tr q (reads c).1 (reads c).2).inputTape with
    | zero => trivial
    | pos =>
      simp only [hm, show (SignType.pos = SignType.neg) = False from by simp, decide_false,
        Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hg ⊢
      rw [sv_sgn H none _ (by simp [tvOf]; omega), sv_sgn H none _ (by simp [tvOf]; omega)] at hg
      simpa [sgnZ, tvOf, avOf] using hg
    | neg =>
      simp only [hm, decide_true, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hg ⊢
      rw [sv_sgn H none _ (by simp [tvOf]; omega), sv_sgn H none _ (by simp [tvOf]; omega)] at hg
      simpa [sgnZ, tvOf, avOf, SignType.neg_eq_neg_one] using hg

/-- The input cells far from the head are blank. -/
theorem RI_far (c : Cfg M.k Bool M.State x) (d : ℤ) (hd : x.length + 1 < d.natAbs) :
    RI c d = none := by
  unfold RI
  rw [xhat_eq_none]
  have := c.inputPos.isLt
  omega

/-- The local input rule only reads the cells `m`, `d` and `d + m`. -/
theorem ruleI_congr (oq : Option M.State) (ρ : Rd M) (d : ℤ) (f g : ℤ → Option Bool)
    (hfg : ∀ e, f e = g e) : ruleI M oq ρ d f = ruleI M oq ρ d g := by
  rw [show f = g from funext hfg]

/-- **Input rows stay correct**: from a correct row `t`, the guessed input cells of row
`t + 1` are the true ones.

**Proof sketch.** By the local input rule (`RI_step`): if `M` is halted, does not move its
input head, or the move is clamped, every cell stays (the "same" half of `in_edge`);
otherwise cell `d` takes the old cell `d ± 1`, read off the edge facts, except at the
outermost cell, which the boundary check blanks (`bd_edge`), as the true row does
(`RI_far`). -/
theorem input_correct (H : AllGood M Ans (W := W) (x := x) xb) {t : ℕ} (ht : t + 1 < 2 ^ W)
    (hc : Correct M Ans W x t) (d : ℤ) (hd : d.natAbs ≤ x.length + 1) :
    cX M Ans none (t + 1) d = RI (M.tm.runFrom (M.tm.initCfg x) (t + 1)) d := by
  have hIH : ∀ e : ℤ, e.natAbs ≤ x.length + 1 →
      cX M Ans none t e = RI (M.tm.runFrom (M.tm.initCfg x) t) e := hc.2.2
  have hE := fun e he1 he2 => in_edge (M := M) (Ans := Ans) (xb := xb) H ht hc e he1 he2
  have hB := bd_edge (M := M) (Ans := Ans) (xb := xb) H ht hc
  simp only at hE hB
  rw [MultiTapeTM.runFrom_succ_eq_step', RI_step]
  generalize M.tm.runFrom (M.tm.initCfg x) t = c at hIH hE hB ⊢
  -- the "same" case: every cell is unchanged
  have hstay : (∀ e : ℤ, -((x.length : ℤ) + 1) ≤ e → e ≤ x.length →
      cX M Ans none (t + 1) e = cX M Ans none t e ∧
        cX M Ans none (t + 1) (e + 1) = cX M Ans none t (e + 1)) →
      cX M Ans none (t + 1) d = RI c d := by
    intro hs
    by_cases hdn : d ≤ x.length
    · rw [(hs d (by omega) hdn).1, hIH d hd]
    · have := (hs x.length (by omega) le_rfl).2
      rw [show d = (x.length : ℤ) + 1 by omega, this, hIH _ (by omega)]
  unfold ruleI
  cases hq : c.state with
  | none =>
    apply hstay
    intro e he1 he2
    have := hE e he1 he2
    simp only [hq] at this
    exact this
  | some q =>
    simp only
    have hm1 : ∀ m : SignType, ((m : ℤ)).natAbs ≤ x.length + 1 := by
      intro m; cases m <;> simp
    cases hm : (M.tm.tr q (reads c).1 (reads c).2).inputTape with
    | zero =>
      simp only [SignType.zero_eq_zero, SignType.coe_zero, add_zero, ite_self]
      apply hstay
      intro e he1 he2
      have := hE e he1 he2
      simp only [hq, hm] at this
      exact this
    | pos =>
      have hcl : ((reads c).1 = none ∧ cX M Ans none t ((SignType.pos : SignType) : ℤ) = none) ↔
          ((reads c).1 = none ∧ RI c ((SignType.pos : SignType) : ℤ) = none) := by
        rw [hIH _ (hm1 _)]
      by_cases hcl' : (reads c).1 = none ∧ RI c ((SignType.pos : SignType) : ℤ) = none
      · rw [if_pos hcl']
        apply hstay
        intro e he1 he2
        have := hE e he1 he2
        simp only [hq, hm] at this
        rwa [if_pos (hcl.mpr hcl')] at this
      · rw [if_neg hcl']
        by_cases hdn : d ≤ x.length
        · have := hE d (by omega) hdn
          simp only [hq, hm] at this
          rw [if_neg (fun h => hcl' (hcl.mp h))] at this
          rw [this, hIH _ (by omega)]
          simp [SignType.pos_eq_one]
        · have := hB
          simp only [hq, hm] at this
          have hdd : d = (x.length : ℤ) + 1 := by omega
          rw [hdd]
          rcases this with h | h
          · exact absurd (hcl.mp h) hcl'
          · rw [h, RI_far c _ (by simp; omega)]
    | neg =>
      have hcl : ((reads c).1 = none ∧ cX M Ans none t ((SignType.neg : SignType) : ℤ) = none) ↔
          ((reads c).1 = none ∧ RI c ((SignType.neg : SignType) : ℤ) = none) := by
        rw [hIH _ (hm1 _)]
      by_cases hcl' : (reads c).1 = none ∧ RI c ((SignType.neg : SignType) : ℤ) = none
      · rw [if_pos hcl']
        apply hstay
        intro e he1 he2
        have := hE e he1 he2
        simp only [hq, hm] at this
        rwa [if_pos (hcl.mpr hcl')] at this
      · rw [if_neg hcl']
        by_cases hdn : -(x.length : ℤ) ≤ d
        · have := hE (d - 1) (by omega) (by omega)
          simp only [hq, hm, sub_add_cancel] at this
          rw [if_neg (fun h => hcl' (hcl.mp h))] at this
          rw [this, hIH _ (by omega)]
          simp [SignType.neg_eq_neg_one, sub_eq_add_neg]
        · have := hB
          simp only [hq, hm] at this
          have hdd : d = -((x.length : ℤ) + 1) := by omega
          rw [hdd]
          rcases this with h | h
          · exact absurd (hcl.mp h) hcl'
          · rw [h, RI_far c _ (by simp [SignType.neg_eq_neg_one]; omega)]

/-- **Correct rows stay correct.** -/
theorem correct_succ (H : AllGood M Ans (W := W) (x := x) xb) {t : ℕ} (ht : t + 1 < 2 ^ W)
    (hc : Correct M Ans W x t) : Correct M Ans W x (t + 1) := by
  refine ⟨?_, fun h d hd => work_correct H ht hc h d hd, fun d hd => input_correct H ht hc d hd⟩
  intro σ'
  set c := M.tm.runFrom (M.tm.initCfg x) t with hcdef
  have hg := H t 0 0 (by omega) (Nat.two_pow_pos W) (by omega) (.stepSt (SS c) (reads c) σ')
  have hcl := claims_of_correct hc (by omega) 0 0 (xb 0)
  simp only [goodF] at hg
  rw [← hcdef] at hcl
  rw [hcl] at hg
  simp only [NumVal, ht, decide_true, Bool.true_and, Bool.not_true, Bool.false_or,
    tvOf, avOf, beq_iff_eq] at hg
  rw [hg, MultiTapeTM.runFrom_succ_eq_step', SS_step]

/-- **Every row is correct** (induction on time). -/
theorem correct_all (H : AllGood M Ans (W := W) (x := x) xb)
    (hxb : ∀ j (hj : j < x.length), xb j = x[j]) :
    ∀ t, t < 2 ^ W → Correct M Ans W x t := by
  intro t
  induction t with
  | zero => intro _; exact correct_zero H hxb
  | succ t ih => intro ht; exact correct_succ H ht (ih (by omega))

/-- **Soundness of the checks** [AB09, proof of Thm 6.20]: if the guessed tableau passes
every check on every instance, then the true run of `M` on `x` is halted at time
`2^W - 1` with output summary `one true` (output `[true]`).

**Proof sketch.** By `correct_all`, every guessed row is the true one; the final check
says the guessed state at time `2^W - 1` is `(halted, one true)`. -/
theorem sound_numeric (H : AllGood M Ans (W := W) (x := x) xb)
    (hxb : ∀ j (hj : j < x.length), xb j = x[j]) :
    SS (M.tm.runFrom (M.tm.initCfg x) (2 ^ W - 1)) = (none, OutReg.one true) := by
  have hpos := Nat.two_pow_pos W
  have hf := H (2 ^ W - 1) 0 0 (by omega) hpos (by omega) .final
  simp only [goodF, NumVal_ans, tvOf, avOf] at hf
  have hc := (correct_all H hxb (2 ^ W - 1) (by omega)).1 (none, OutReg.one true)
  rw [hf] at hc
  exact (of_decide_eq_true hc.symm).symm

end sound

end Complexity.Meyer
