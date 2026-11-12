/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.MeyerVerifier

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Meyer's theorem: soundness of the checks

If a guessed tableau passes all checks of `MeyerVerifier.lean`, it is the true
head-relative tableau of `M` on `x` — row by row, by induction on time — so its final
row, which the checks require to be halted with output `[true]`, shows that `M` accepts
`x` ([AB09, proof of Thm 6.20]: "the correctness of the transcript implicitly computed
by this circuit can be expressed as a coNP predicate").

The argument is carried out for an abstract *numeric* oracle `Ans sel t a` (the guessed
answer at selector `sel`, time `t`, offset `a`); `MeyerComplete.lean` connects it with
the verifier's atoms.

## Main definitions

* `Complexity.Meyer.NumVal` — the atom valuation of a numeric instance `(t, a, j)`.
* `Complexity.Meyer.sv`, `Complexity.Meyer.cX` — guessed symbols, by sign and by offset.

## Main results

* `Complexity.Meyer.correct_zero` — the guessed initial row is correct.
* `Complexity.Meyer.work_correct` — correct rows stay correct on the work tapes.

The input tapes, the induction and the final row are in `MeyerSoundInput.lean`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§6.4, Theorem 6.20, pp. 114–115.)
-/

namespace Complexity.Meyer

open Turing Complexity.TimeHierarchy

variable (M : FinTM Bool)

/-! ### Numeric instances -/

/-- The time value of a time word at time `t` (width `W`). -/
def tvOf (W t : ℕ) : TW → ℕ
  | .tc => t
  | .tn => t + 1
  | .t0 => 0
  | .t1 => 2 ^ W - 1

/-- The offset value of an offset word at offset `a` and input offset `j`. -/
def avOf (a j : ℕ) : AW → ℕ
  | .ac => a
  | .an => a + 1
  | .a0 => 0
  | .a1 => 1
  | .aj => j
  | .aj1 => j + 1

/-- **The atom valuation of a numeric instance** `(t, a, j)` for the numeric oracle `Ans`,
inputs of length `n`, width `W`, and input bit `xb`. -/
def NumVal (Ans : Sel M → ℕ → ℕ → Bool) (W n t a j : ℕ) (xb : Bool) :
    Atom M.State M.k → Bool
  | .ans sel T A => Ans sel (tvOf W t T) (avOf a j A)
  | .lenAll => true
  | .tNotOnes => decide (t + 1 < 2 ^ W)
  | .aNotOnes => decide (a + 1 < 2 ^ W)
  | .aZero => decide (a = 0)
  | .jZero => decide (j = 0)
  | .jLtN => decide (j < n)
  | .jLeN => decide (j ≤ n)
  | .jEqN1 => decide (j = n + 1)
  | .xbit => xb

variable (Ans : Sel M → ℕ → ℕ → Bool)

/-- The guessed symbol at tape `τ`, sign `s`, time `t`, offset `a`. -/
def sv (τ : Option (Fin M.k)) (s : Bool) (t a : ℕ) : Option Bool :=
  if Ans (.sym τ s true) t a then none else some (Ans (.sym τ s false) t a)

/-- The guessed symbol at tape `τ`, time `t`, signed offset `d` (canonical sign). -/
def cX (τ : Option (Fin M.k)) (t : ℕ) (d : ℤ) : Option Bool :=
  sv M Ans τ (decide (d < 0)) t d.natAbs

section valuation

variable (W n t a j : ℕ) (xb : Bool)

/-- The guessed symbol of a numeric valuation is the numeric guessed symbol. -/
@[simp] theorem symvA_NumVal (τ : Option (Fin M.k)) (s : Bool) (T : TW) (A : AW) :
    symvA M (NumVal M Ans W n t a j xb) τ s T A = sv M Ans τ s (tvOf W t T) (avOf a j A) := rfl

/-- The guessed state claim of a numeric valuation is the oracle's state answer. -/
@[simp] theorem stA_NumVal (σ : Option M.State × OutReg) (T : TW) :
    stA M (NumVal M Ans W n t a j xb) σ T = Ans (.st σ.1 σ.2) (tvOf W t T) 0 := rfl

/-- A numeric valuation answers queries with the numeric oracle. -/
@[simp] theorem NumVal_ans (sel : Sel M) (T : TW) (A : AW) :
    NumVal M Ans W n t a j xb (.ans sel T A) = Ans sel (tvOf W t T) (avOf a j A) := rfl

end valuation

/-! ### Decoding symbols -/

/-- The two selector bits of a symbol decode back to it. -/
theorem decode_symBit (v : Option Bool) :
    (if symBit true v then none else some (symBit false v)) = v := by
  rcases v with _ | _ | _ <;> simp [symBit]

/-! ### Edges -/

/-- The sign of the edge `(e, e + 1)`: negative edges have `e ≤ -1`. -/
def sE (e : ℤ) : Bool := decide (e < 0)

/-- The magnitude word value of the edge `(e, e + 1)`: `e` for `e ≥ 0`, `-e - 1` for
`e < 0`. -/
def aE (e : ℤ) : ℕ := if e < 0 then (-e - 1).toNat else e.toNat

/-- The first cell of an edge is `e`. -/
theorem edge_c1 (e : ℤ) : sgnZ (sE e) (if sE e then aE e + 1 else aE e) = e := by
  unfold sgnZ sE aE; by_cases h : e < 0 <;> simp [h]; omega

/-- The second cell of an edge is `e + 1`. -/
theorem edge_c2 (e : ℤ) : sgnZ (sE e) (if sE e then aE e else aE e + 1) = e + 1 := by
  unfold sgnZ sE aE; by_cases h : e < 0 <;> simp [h] <;> omega

/-- The edge `(-1, 0)` is the negative edge of magnitude `0`. -/
theorem edge_E1 (e : ℤ) : (sE e && decide (aE e = 0)) = decide (e + 1 = 0) := by
  unfold sE aE; by_cases h : e < 0 <;> simp [h] <;> omega

/-- The edge `(0, 1)` is the nonnegative edge of magnitude `0`. -/
theorem edge_E0 (e : ℤ) : (!sE e && decide (aE e = 0)) = decide (e = 0) := by
  unfold sE aE; by_cases h : e < 0 <;> simp [h] <;> omega

/-- The magnitude of an edge, exactly. -/
theorem aE_add_one (e : ℤ) : aE e + 1 = if e < 0 then e.natAbs else e.natAbs + 1 := by
  unfold aE; split_ifs <;> omega

/-! ### Soundness -/

section sound

variable {W : ℕ} {x : List Bool} (xb : ℕ → Bool)

/-- **The hypothesis of soundness**: all checks pass on all numeric instances in range. -/
def AllGood : Prop :=
  ∀ t a j, t < 2 ^ W → a < 2 ^ W → j ≤ x.length + 1 →
    ∀ π, goodF M (NumVal M Ans W x.length t a j (xb j)) π = true

variable {M Ans xb}

/-- The two codes of offset `0` agree. -/
theorem sv_negZero (H : AllGood M Ans (W := W) (x := x) xb) (τ : Option (Fin M.k)) (t : ℕ)
    (ht : t < 2 ^ W) : sv M Ans τ true t 0 = sv M Ans τ false t 0 := by
  have h1 := H t 0 0 ht (Nat.two_pow_pos W) (by omega) (.negZero τ true)
  have h2 := H t 0 0 ht (Nat.two_pow_pos W) (by omega) (.negZero τ false)
  simp only [goodF, NumVal_ans, tvOf, avOf, beq_iff_eq] at h1 h2
  simp [sv, h1, h2]

/-- Guessed symbols by sign are guessed symbols by signed offset. -/
theorem sv_sgn (H : AllGood M Ans (W := W) (x := x) xb) (τ : Option (Fin M.k)) (t : ℕ)
    (ht : t < 2 ^ W) (s : Bool) (a : ℕ) : sv M Ans τ s t a = cX M Ans τ t (sgnZ s a) := by
  unfold cX sgnZ
  cases s
  · have h0 : ¬ ((a : ℤ) < 0) := by omega
    simp [h0]
  · rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp [sv_negZero H τ t ht]
    · simp [ha]

/-- The guessed symbol at offset `0` uses the nonnegative code. -/
theorem cX_zero (τ : Option (Fin M.k)) (t : ℕ) : cX M Ans τ t 0 = sv M Ans τ false t 0 := by
  simp [cX]

variable (M Ans W x) in
/-- **Correctness of the guessed row `t`**: the state claims, the work cells in the light
cone `|d| + t ≤ 2^W - 1`, and the input cells `|d| ≤ |x| + 1` are those of the true
run. -/
def Correct (t : ℕ) : Prop :=
  (∀ σ : Option M.State × OutReg,
    Ans (.st σ.1 σ.2) t 0 = decide (σ = SS (M.tm.runFrom (M.tm.initCfg x) t))) ∧
  (∀ (h : Fin M.k) (d : ℤ), d.natAbs + t ≤ 2 ^ W - 1 →
    cX M Ans (some h) t d = RW (M.tm.runFrom (M.tm.initCfg x) t) h d) ∧
  (∀ d : ℤ, d.natAbs ≤ x.length + 1 →
    cX M Ans none t d = RI (M.tm.runFrom (M.tm.initCfg x) t) d)

/-- A correct row claims its true state and reads. -/
theorem claims_of_correct {t : ℕ} (hc : Correct M Ans W x t) (ht : t < 2 ^ W) (a j : ℕ)
    (b : Bool) :
    claims M (NumVal M Ans W x.length t a j b) .tc (SS (M.tm.runFrom (M.tm.initCfg x) t))
      (reads (M.tm.runFrom (M.tm.initCfg x) t)) = true := by
  obtain ⟨h1, h2, h3⟩ := hc
  simp only [claims, stA_NumVal, symvA_NumVal, tvOf, avOf, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [h1]; simp
  · rw [← cX_zero, h3 0 (by simp)]; rfl
  · intro h
    rw [← cX_zero, h2 h 0 (by simp; omega)]; rfl

/-- The guessed initial input cell is the padded input. -/
theorem xin_eq (hxb : ∀ j (hj : j < x.length), xb j = x[j]) (d : ℤ) :
    (if (decide (d < 0) && !decide (d.natAbs = 0)) = true then none
      else if d.natAbs < x.length then some (xb d.natAbs) else none) = xhat x (1 + d) := by
  unfold xhat
  by_cases hd : d < 0
  · have h1 : d.natAbs ≠ 0 := by omega
    simp [hd, h1]
  · have hj : (1 + d - 1).toNat = d.natAbs := by omega
    simp only [hd, decide_false, Bool.false_and, Bool.false_eq_true, if_false,
      show (1 : ℤ) ≤ 1 + d by omega, if_true, hj]
    by_cases hn : d.natAbs < x.length
    · simp [hn, hxb _ hn]
    · simp [hn]

/-- **The base row is correct.**

**Proof sketch.** The initial-row checks give the guessed state `(q₀, empty)`, blank work
cells and the input cells `x̂(1 + d)` (`xin_eq`), which are the cells of the initial
configuration. -/
theorem correct_zero (H : AllGood M Ans (W := W) (x := x) xb)
    (hxb : ∀ j (hj : j < x.length), xb j = x[j]) :
    Correct M Ans W x 0 := by
  have hW : 0 < 2 ^ W := Nat.two_pow_pos W
  refine ⟨?_, ?_, ?_⟩
  · intro σ
    have h := H 0 0 0 hW hW (by omega) (.initSt σ.1 σ.2)
    simp only [goodF, NumVal_ans, tvOf, avOf, beq_iff_eq] at h
    rw [h, MultiTapeTM.runFrom_zero, SS_init]
  · intro h d hd
    have hb : ∀ b, Ans (.sym (some h) (decide (d < 0)) b) 0 d.natAbs = symBit b none := by
      intro b
      have := H 0 d.natAbs 0 hW (by omega) (by omega) (.initW h (decide (d < 0)) b)
      simpa only [goodF, NumVal_ans, tvOf, avOf, beq_iff_eq] using this
    simp only [cX, sv, hb, decode_symBit, MultiTapeTM.runFrom_zero, RW_init]
  · intro d hd
    have hb : ∀ b, Ans (.sym none (decide (d < 0)) b) 0 d.natAbs =
        symBit b (if (decide (d < 0) && !decide (d.natAbs = 0)) = true then none
          else if d.natAbs < x.length then some (xb d.natAbs) else none) := by
      intro b
      have := H 0 0 d.natAbs hW hW hd (.initI (decide (d < 0)) b)
      simpa only [goodF, NumVal_ans, tvOf, avOf, beq_iff_eq, xinV, NumVal,
        decide_eq_true_eq] using this
    simp only [cX, sv, hb, decode_symBit, MultiTapeTM.runFrom_zero, RI_init]
    exact xin_eq hxb d

/-- `avOf` commutes with a sign-selected word. -/
theorem avOf_ite (a j : ℕ) (s : Bool) (A B : AW) :
    avOf a j (if s then A else B) = if s then avOf a j A else avOf a j B := by
  cases s <;> rfl

/-- **The work-tape edge facts**: the step check on the edge `(e, e + 1)` of tape `h` at a
correct row `t`, in terms of guessed cells.

**Proof sketch.** Instantiate the work-step check at the edge `(sE e, aE e)` with the true
claims (`claims_of_correct`); translate its sign/magnitude cells to signed offsets
(`sv_sgn`, `edge_c1`, `edge_c2`, `edge_E0`, `edge_E1`). -/
theorem work_edge (H : AllGood M Ans (W := W) (x := x) xb) {t : ℕ} (ht : t + 1 < 2 ^ W)
    (hc : Correct M Ans W x t) (h : Fin M.k) (e : ℤ) (he : aE e + 1 < 2 ^ W) :
    let c := M.tm.runFrom (M.tm.initCfg x) t
    match c.state with
    | none => cX M Ans (some h) (t + 1) e = cX M Ans (some h) t e
    | some q =>
      let ws : Option Bool := wsym ((M.tm.tr q (reads c).1 (reads c).2).workTapes h).1 ((reads c).2 h)
      match ((M.tm.tr q (reads c).1 (reads c).2).workTapes h).2 with
      | .pos => cX M Ans (some h) (t + 1) e =
          if e + 1 = 0 then ws else cX M Ans (some h) t (e + 1)
      | .neg => cX M Ans (some h) (t + 1) (e + 1) =
          if e = 0 then ws else cX M Ans (some h) t e
      | .zero => cX M Ans (some h) (t + 1) e =
          if e = 0 then ws else cX M Ans (some h) t e := by
  intro c
  have hg := H t (aE e) 0 (by omega) (by omega) (by omega)
    (.stepW (SS c) (reads c) h (sE e))
  have hcl := claims_of_correct hc (by omega) (aE e) 0 (xb 0)
  simp only [goodF] at hg
  rw [hcl] at hg
  simp only [NumVal, ht, decide_true, he, Bool.true_and, Bool.not_true, Bool.false_or] at hg
  have s1 : ∀ T, sv M Ans (some h) (sE e) (tvOf W t T) (if sE e then aE e + 1 else aE e) =
      cX M Ans (some h) (tvOf W t T) e := by
    intro T
    rw [sv_sgn H _ _ ?_ _ _, edge_c1]
    cases T <;> simp [tvOf] <;> omega
  have s2 : ∀ T, sv M Ans (some h) (sE e) (tvOf W t T) (if sE e then aE e else aE e + 1) =
      cX M Ans (some h) (tvOf W t T) (e + 1) := by
    intro T
    rw [sv_sgn H _ _ ?_ _ _, edge_c2]
    cases T <;> simp [tvOf] <;> omega
  simp only [workOK, symvA_NumVal, avOf_ite, NumVal] at hg
  simp only [avOf, edge_E0, edge_E1] at hg
  have hsc : (SS c).1 = c.state := rfl
  rw [hsc] at hg
  cases hq : c.state with
  | none =>
    simp only [hq, decide_eq_true_eq] at hg
    rw [s1 .tn, s1 .tc] at hg
    simpa [tvOf] using hg
  | some q =>
    simp only [hq] at hg ⊢
    cases hm : ((M.tm.tr q (reads c).1 (reads c).2).workTapes h).2 with
    | zero =>
      simp only [hm, decide_eq_true_eq] at hg ⊢
      rw [s1 .tn, s1 .tc] at hg
      simpa [tvOf] using hg
    | pos =>
      simp only [hm, decide_eq_true_eq] at hg ⊢
      rw [s1 .tn, s2 .tc] at hg
      simpa [tvOf] using hg
    | neg =>
      simp only [hm, decide_eq_true_eq] at hg ⊢
      rw [s2 .tn, s1 .tc] at hg
      simpa [tvOf] using hg

/-- The local work rule only reads the cells `d` and `d + m`. -/
theorem ruleW_congr (oq : Option M.State) (ρ : Rd M) (h : Fin M.k) (d : ℤ)
    (f g : ℤ → Option Bool) (hfg : ∀ e : ℤ, e.natAbs ≤ d.natAbs + 1 → f e = g e) :
    ruleW M oq ρ h d f = ruleW M oq ρ h d g := by
  unfold ruleW
  cases oq with
  | none => exact hfg d (by omega)
  | some q =>
    simp only
    generalize ((M.tm.tr q ρ.1 ρ.2).workTapes h).2 = m
    split_ifs
    · rfl
    · apply hfg; cases m <;> simp <;> omega

/-- **The work rule at a correct row**: the guessed row `t + 1` follows the local rule
from the guessed row `t`, inside the light cone.

**Proof sketch.** For moves `+1` and `0` use the edge starting at `d`, for move `-1` the
edge ending at `d` (`work_edge` at `d - 1`); each gives the corresponding clause of `ruleW`.
-/
theorem work_rule (H : AllGood M Ans (W := W) (x := x) xb) {t : ℕ} (ht : t + 1 < 2 ^ W)
    (hc : Correct M Ans W x t) (h : Fin M.k) (d : ℤ) (hd : d.natAbs + (t + 1) ≤ 2 ^ W - 1) :
    cX M Ans (some h) (t + 1) d =
      ruleW M (M.tm.runFrom (M.tm.initCfg x) t).state (reads (M.tm.runFrom (M.tm.initCfg x) t))
        h d (cX M Ans (some h) t) := by
  have hed := work_edge H ht hc h d (by rw [aE_add_one]; split_ifs <;> omega)
  have hed' := work_edge H ht hc h (d - 1) (by rw [aE_add_one]; split_ifs <;> omega)
  simp only at hed hed'
  unfold ruleW
  cases hq : (M.tm.runFrom (M.tm.initCfg x) t).state with
  | none => simp only [hq] at hed; exact hed
  | some q =>
    simp only [hq] at hed hed' ⊢
    cases hm : ((M.tm.tr q (reads (M.tm.runFrom (M.tm.initCfg x) t)).1
      (reads (M.tm.runFrom (M.tm.initCfg x) t)).2).workTapes h).2 with
    | zero => simp only [hm] at hed; simpa using hed
    | pos => simp only [hm] at hed; simpa using hed
    | neg =>
      simp only [hm, sub_add_cancel] at hed'
      rw [hed']
      have e2 : d + ((SignType.neg : SignType) : ℤ) = d - 1 := by
        simp [SignType.neg_eq_neg_one, sub_eq_add_neg]
      simp only [e2]

/-- **Work rows stay correct**: from a correct row `t`, the guessed work cells of row
`t + 1` in the light cone are the true ones. -/
theorem work_correct (H : AllGood M Ans (W := W) (x := x) xb) {t : ℕ} (ht : t + 1 < 2 ^ W)
    (hc : Correct M Ans W x t) (h : Fin M.k) (d : ℤ) (hd : d.natAbs + (t + 1) ≤ 2 ^ W - 1) :
    cX M Ans (some h) (t + 1) d = RW (M.tm.runFrom (M.tm.initCfg x) (t + 1)) h d := by
  rw [work_rule H ht hc h d hd, MultiTapeTM.runFrom_succ_eq_step', RW_step]
  apply ruleW_congr
  intro e he
  exact hc.2.1 h e (by omega)

end sound

end Complexity.Meyer
