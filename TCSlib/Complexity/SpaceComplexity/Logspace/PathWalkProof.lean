/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Logspace.PathWalkMachine
import TCSlib.Complexity.SpaceComplexity.Machines.NARMProof

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The nondeterministic walk decides `PATH` in `NL`

[AB09, §4.1.2]: the walk machine `Complexity.LogProg.pathA` of
`TCSlib.Complexity.SpaceComplexity.Logspace.PathWalkMachine` decides the raw `PATH` language
`Complexity.pathRawLang` with registers bounded by `4 (|x| + 1)`, so the language is in `NL`
(`Complexity.pathRawLang_mem_NL`, by `Complexity.LogProg.narm_decides_poly`).

The proof is by the continuation semantics of
`TCSlib.Complexity.SpaceComplexity.Machines.NARMKit`: one lemma per loop of the machine
states that every branch from the loop head terminates (with registers bounded) and that
some branch accepts iff the loop's condition on the input holds and the continuation
accepts. Composed from the start (`Complexity.LogProg.ps_start`), some branch accepts iff
`Complexity.PathAcc x`, which is membership in `pathRawLang` (`Complexity.pathAcc_iff`).

## Main definitions

* `Complexity.LogProg.PReg.zero` — the initial register file.

## Main results

* `Complexity.LogProg.ps_unary`, `Complexity.LogProg.ps_mat`, `Complexity.LogProg.ps_sphase`,
  `Complexity.LogProg.ps_tphase` — the input checks.
* `Complexity.LogProg.ps_start` — the semantics of the machine.
* `Complexity.pathRawLang_mem_NL` — the raw `PATH` language is in `NL`. [AB09, §4.1.2]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.2.)
-/

namespace Complexity

open Turing

namespace LogProg

open PathLabel PathWalkTac

variable {x : List Bool} {B : ℕ}

/-- **The target check**: the binary digits of the scratch copy are compared with the input
suffix from the pointer, which must end the input.

**Proof sketch.** Strong induction on the copy `w`. At `w = 0` the length query accepts
exactly at the end of the input. Otherwise the pointer must be inside the input, the bit
under it must be the parity of `w` (`bits_eq_cons`, `plainAt_cons`), and the check recurs
on `w / 2` one position later. -/
lemma ps_tcmp (hB : 2 * x.length + 2 ≤ B) (K : Prop) (σ : PReg) (hσ : σ.Le B)
    (hp : σ.p ≤ x.length)
    (hK : PlainAt x σ.p (Nat.bits σ.tmp) → PS x B w0 { σ with p := x.length, tmp := 0 } K) :
    PS x B ttt σ (PlainAt x σ.p (Nat.bits σ.tmp) ∧ K) := by
  suffices H : ∀ w (σ : PReg), σ.tmp = w → σ.Le B → σ.p ≤ x.length →
      (PlainAt x σ.p (Nat.bits σ.tmp) → PS x B w0 { σ with p := x.length, tmp := 0 } K) →
      PS x B ttt σ (PlainAt x σ.p (Nat.bits σ.tmp) ∧ K) from H _ σ rfl hσ hp hK
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro σ hw hσ hp hK
  rcases Nat.eq_zero_or_pos w with rfl | hwpos
  · simp only [hw, Nat.zero_bits] at hK ⊢
    refine NSem.jz_pos rfl (PReg.reg hσ _ _) (by simpa using hw) ?_
    by_cases hpx : σ.p < x.length
    · refine (NSem.call_pos rfl (PReg.reg hσ _ _)
        (by simp only [PReg.v_0, pathOr_len, decide_eq_true_eq]; exact hpx)
        (NSem.ret rfl (PReg.reg hσ _ _))).congr ?_
      simp only [PlainAt, List.length_nil]
      simp; omega
    · have hd : PlainAt x σ.p [] := ⟨fun i hi => absurd hi (by simp), by simp; omega⟩
      refine NSem.call_neg rfl (PReg.reg hσ _ _)
        (by simp only [PReg.v_0, pathOr_len, decide_eq_false_iff_not]; exact hpx) ?_
      exact PS.of_eq (by ext <;> simp <;> omega) ((hK hd).congr ⟨fun h => ⟨hd, h⟩, fun h => h.2⟩)
  · have hw0 : w ≠ 0 := by omega
    have hbits := bits_eq_cons hw0
    rw [hw, hbits] at hK ⊢
    refine NSem.jz_neg rfl (PReg.reg hσ _ _) (by simp only [PReg.v_6]; omega) ?_
    by_cases hpx : σ.p < x.length
    · refine NSem.call_pos rfl (PReg.reg hσ _ _)
        (by simp only [PReg.v_0, pathOr_len, decide_eq_true_eq]; exact hpx) ?_
      have hnext : ∀ b : Bool, b = decide (w % 2 = 1) → x.getD σ.p false = b →
          PS x B tad σ (PlainAt x σ.p (decide (w % 2 = 1) :: Nat.bits (w / 2)) ∧ K) := by
        intro b hb h0
        refine NSem.inc rfl (PReg.reg hσ _ _) ?_
        pw_regs
        refine NSem.half rfl (PReg.reg (by pw_le) _ _) ?_
        pw_regs
        have hrec := ih (w / 2) (by omega) { σ with p := σ.p + 1, tmp := w / 2 } rfl
          (by pw_le) (by dsimp only; omega) (fun hd => by
            refine PS.of_eq (by ext <;> simp) (hK ?_)
            rw [plainAt_cons]; exact ⟨hb ▸ h0, hd⟩)
        refine PS.of_eq (σ' := { σ with p := σ.p + 1, tmp := w / 2 })
          (by pw_ext') (hrec.congr ?_)
        dsimp only
        rw [plainAt_cons, ← hb, h0]
        simp
      have hbad : ∀ b : Bool, b ≠ decide (w % 2 = 1) → x.getD σ.p false = b →
          ¬ PlainAt x σ.p (decide (w % 2 = 1) :: Nat.bits (w / 2)) := by
        intro b hb h0 hP
        rw [plainAt_cons, h0] at hP
        exact hb hP.1
      by_cases hodd : w % 2 = 1
      · refine NSem.jodd_pos rfl (PReg.reg hσ _ _) (by simp only [PReg.v_6, hw]; exact hodd) ?_
        cases hb0 : x.getD σ.p false
        · refine (NSem.call_neg rfl (PReg.reg hσ _ _) (by simp only [PReg.v_0, pathOr_bit, hb0])
            (NSem.ret rfl (PReg.reg hσ _ _))).congr ?_
          simp only [Bool.false_eq_true, false_iff, not_and]
          exact fun h _ => hbad false (by simp [hodd]) hb0 h
        · refine NSem.call_pos rfl (PReg.reg hσ _ _) (by simp only [PReg.v_0, pathOr_bit, hb0]) ?_
          exact hnext true (by simp [hodd]) hb0
      · refine NSem.jodd_neg rfl (PReg.reg hσ _ _) (by simp only [PReg.v_6, hw]; exact hodd) ?_
        cases hb0 : x.getD σ.p false
        · refine NSem.call_neg rfl (PReg.reg hσ _ _) (by simp only [PReg.v_0, pathOr_bit, hb0]) ?_
          exact hnext false (by simp [hodd]) hb0
        · refine (NSem.call_pos rfl (PReg.reg hσ _ _) (by simp only [PReg.v_0, pathOr_bit, hb0])
            (NSem.ret rfl (PReg.reg hσ _ _))).congr ?_
          simp only [Bool.false_eq_true, false_iff, not_and]
          exact fun h _ => hbad true (by simp [hodd]) hb0 h
    · refine (NSem.call_neg rfl (PReg.reg hσ _ _)
        (by simp only [PReg.v_0, pathOr_len, decide_eq_false_iff_not]; exact hpx)
        (NSem.ret rfl (PReg.reg hσ _ _))).congr ?_
      simp only [Bool.false_eq_true, false_iff, not_and]
      intro h _
      have := h.2
      simp only [List.length_cons] at this
      omega

/-- **Guessing and checking the target.**

**Proof sketch.** `nsem_guess` on the target register, then `nsem_copy` into the scratch
register and `ps_tcmp`. -/
lemma ps_tphase (hB : 2 * x.length + 2 ≤ B) (K : ℕ → Prop) (σ : PReg) (hσ : σ.Le B)
    (ht : σ.t = 0) (htmp : σ.tmp = 0) (hp : σ.p ≤ x.length) (hn : σ.n ≤ x.length)
    (hK : ∀ j, j < σ.n → PlainAt x σ.p (Nat.bits j) →
      PS x B w0 { σ with t := j, p := x.length, tmp := 0 } (K j)) :
    PS x B tg σ (∃ j, j < σ.n ∧ PlainAt x σ.p (Nat.bits j) ∧ K j) := by
  refine (nsem_guess pathA pathOr x B 5 1 (by decide) tg tc tm tcp rej rfl rfl rfl rfl
    (fun j => PlainAt x σ.p (Nat.bits j) ∧ K j) σ.v (PReg.reg hσ none none)
    (by simp only [PReg.v_5, PReg.v_1]; omega) (fun j hj1 hj2 => ?_)).congr ?_
  · simp only [PReg.v_5, PReg.v_1] at hj1 hj2
    pw_regs
    refine nsem_copy pathA pathOr x B 6 5 (by decide) tcp tbp ttt rfl rfl _ _
      (PReg.reg (by pw_le) none none) (by simp; omega) ?_
    pw_regs
    refine ps_tcmp hB _ _ (by pw_le) (by simp; omega) fun hd => ?_
    simp only at hd ⊢
    exact PS.of_eq (by ext <;> simp) (hK j hj2 hd)
  · simp only [PReg.v_5, PReg.v_1, ht]
    exact ⟨fun ⟨j, _, h⟩ => ⟨j, h⟩, fun ⟨j, h⟩ => ⟨j, Nat.zero_le _, h⟩⟩

/-- **The source check**: the binary digits of the scratch copy are compared with the
doubled field at the pointer, followed by the separator.

**Proof sketch.** Strong induction on the copy `w`. At `w = 0` the next aligned pair must be
the separator `01`. Otherwise both bits of the next aligned pair must be the parity of `w`
(`bits_eq_cons`, `dblAt_cons`), and the check recurs on `w / 2` two positions later. -/
lemma ps_scmp (K : Prop) (σ : PReg) (hσ : σ.Le B)
    (hp : σ.p + 2 * (Nat.bits σ.tmp).length + 2 ≤ B)
    (hK : DblAt x σ.p (Nat.bits σ.tmp) →
      PS x B tg { σ with p := σ.p + 2 * (Nat.bits σ.tmp).length + 2, tmp := 0 } K) :
    PS x B stt σ (DblAt x σ.p (Nat.bits σ.tmp) ∧ K) := by
  suffices H : ∀ w (σ : PReg), σ.tmp = w → σ.Le B → σ.p + 2 * (Nat.bits σ.tmp).length + 2 ≤ B →
      (DblAt x σ.p (Nat.bits σ.tmp) →
        PS x B tg { σ with p := σ.p + 2 * (Nat.bits σ.tmp).length + 2, tmp := 0 } K) →
      PS x B stt σ (DblAt x σ.p (Nat.bits σ.tmp) ∧ K) from H _ σ rfl hσ hp hK
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro σ hw hσ hp hK
  rcases Nat.eq_zero_or_pos w with rfl | hwpos
  · simp only [hw, Nat.zero_bits] at hp hK ⊢
    refine NSem.jz_pos rfl (PReg.reg hσ _ _) (by simpa using hw) ?_
    have hD : ∀ (b0 b1 : Bool), x.getD σ.p false = b0 → x.getD (σ.p + 1) false = b1 →
        (DblAt x σ.p [] ↔ b0 = false ∧ b1 = true) := by
      intro b0 b1 h0 h1
      simp only [DblAt, List.length_nil, Nat.mul_zero, Nat.add_zero, h0, h1]
      simp
    cases hb0 : x.getD σ.p false
    · refine NSem.call_neg rfl (PReg.reg hσ _ _) (by simp only [PReg.v_0, pathOr_bit, hb0]) ?_
      refine NSem.inc rfl (PReg.reg (by pw_le) _ _) ?_
      pw_regs
      cases hb1 : x.getD (σ.p + 1) false
      · refine (NSem.call_neg rfl (PReg.reg (by pw_le) _ _) (by simp only [PReg.v_0, pathOr_bit, hb1])
          (NSem.ret rfl (PReg.reg (by pw_le) _ _))).congr ?_
        rw [hD _ _ hb0 hb1]; simp
      · refine NSem.call_pos rfl (PReg.reg (by pw_le) _ _)
          (by simp only [PReg.v_0, pathOr_bit, hb1]) ?_
        refine NSem.inc rfl (PReg.reg (by pw_le) _ _) ?_
        pw_regs
        have hd : DblAt x σ.p [] := (hD _ _ hb0 hb1).mpr ⟨rfl, rfl⟩
        exact PS.of_eq (by pw_ext') ((hK hd).congr ⟨fun h => ⟨hd, h⟩, fun h => h.2⟩)
    · refine (NSem.call_pos rfl (PReg.reg hσ _ _) (by simp only [PReg.v_0, pathOr_bit, hb0])
        (NSem.ret rfl (PReg.reg hσ _ _))).congr ?_
      simp only [Bool.false_eq_true, false_iff, not_and]
      intro h _
      have := ((hD true (x.getD (σ.p + 1) false) hb0 rfl).mp h).1
      exact absurd this (by simp)
  · have hw0 : w ≠ 0 := by omega
    have hbits := bits_eq_cons hw0
    rw [hw, hbits] at hp hK ⊢
    simp only [List.length_cons] at hp hK ⊢
    have hlen : 1 ≤ (Nat.bits w).length := by rw [hbits]; simp
    refine NSem.jz_neg rfl (PReg.reg hσ _ _) (by simp only [PReg.v_6]; omega) ?_
    -- the rest of the field, after one checked doubled bit
    have hnext : ∀ b : Bool, b = decide (w % 2 = 1) → x.getD σ.p false = b →
        x.getD (σ.p + 1) false = b →
        PS x B sad { σ with p := σ.p + 1 }
          (DblAt x σ.p (decide (w % 2 = 1) :: Nat.bits (w / 2)) ∧ K) := by
      intro b hb h0 h1
      refine NSem.inc rfl (PReg.reg (by pw_le) _ _) ?_
      pw_regs
      refine NSem.half rfl (PReg.reg (by pw_le) _ _) ?_
      pw_regs
      have hrec := ih (w / 2) (by omega) { σ with p := σ.p + 1 + 1, tmp := w / 2 } rfl
        (by pw_le) (by dsimp only; omega) (fun hd => by
          refine PS.of_eq (by pw_ext') (hK ?_)
          rw [dblAt_cons]; exact ⟨⟨hb ▸ h0, hb ▸ h1⟩, hd⟩)
      refine PS.of_eq (σ' := { σ with p := σ.p + 1 + 1, tmp := w / 2 })
        (by pw_ext') (hrec.congr ?_)
      dsimp only
      rw [dblAt_cons, ← hb, h0, h1]
      simp
    by_cases hodd : w % 2 = 1
    · refine NSem.jodd_pos rfl (PReg.reg hσ _ _) (by simp only [PReg.v_6, hw]; exact hodd) ?_
      cases hb0 : x.getD σ.p false
      · refine (NSem.call_neg rfl (PReg.reg hσ _ _) (by simp only [PReg.v_0, pathOr_bit, hb0])
          (NSem.ret rfl (PReg.reg hσ _ _))).congr ?_
        simp only [Bool.false_eq_true, false_iff, not_and, dblAt_cons, hb0, hodd]
        simp
      · refine NSem.call_pos rfl (PReg.reg hσ _ _) (by simp only [PReg.v_0, pathOr_bit, hb0]) ?_
        refine NSem.inc rfl (PReg.reg (by pw_le) _ _) ?_
        pw_regs
        cases hb1 : x.getD (σ.p + 1) false
        · refine (NSem.call_neg rfl (PReg.reg (by pw_le) _ _)
            (by simp only [PReg.v_0, pathOr_bit, hb1]) (NSem.ret rfl (PReg.reg (by pw_le) _ _))).congr ?_
          simp only [Bool.false_eq_true, false_iff, not_and, dblAt_cons, hb1, hodd]
          simp
        · refine NSem.call_pos rfl (PReg.reg (by pw_le) _ _)
            (by simp only [PReg.v_0, pathOr_bit, hb1]) ?_
          exact hnext true (by simp [hodd]) hb0 hb1
    · refine NSem.jodd_neg rfl (PReg.reg hσ _ _) (by simp only [PReg.v_6, hw]; exact hodd) ?_
      cases hb0 : x.getD σ.p false
      · refine NSem.call_neg rfl (PReg.reg hσ _ _) (by simp only [PReg.v_0, pathOr_bit, hb0]) ?_
        refine NSem.inc rfl (PReg.reg (by pw_le) _ _) ?_
        pw_regs
        cases hb1 : x.getD (σ.p + 1) false
        · refine NSem.call_neg rfl (PReg.reg (by pw_le) _ _)
            (by simp only [PReg.v_0, pathOr_bit, hb1]) ?_
          exact hnext false (by simp [hodd]) hb0 hb1
        · refine (NSem.call_pos rfl (PReg.reg (by pw_le) _ _)
            (by simp only [PReg.v_0, pathOr_bit, hb1]) (NSem.ret rfl (PReg.reg (by pw_le) _ _))).congr ?_
          simp only [Bool.false_eq_true, false_iff, not_and, dblAt_cons, hb1, hodd]
          simp
      · refine (NSem.call_pos rfl (PReg.reg hσ _ _) (by simp only [PReg.v_0, pathOr_bit, hb0])
          (NSem.ret rfl (PReg.reg hσ _ _))).congr ?_
        simp only [Bool.false_eq_true, false_iff, not_and, dblAt_cons, hb0, hodd]
        simp

/-- **Guessing and checking the source.**

**Proof sketch.** `nsem_guess` on the source register, then `nsem_copy` into the scratch
register and `ps_scmp`; the bound `|bits j| ≤ j < n` keeps the pointer below `B`. -/
lemma ps_sphase (K : ℕ → Prop) (σ : PReg) (hσ : σ.Le B)
    (hs : σ.s = 0) (htmp : σ.tmp = 0) (hp : σ.p + 2 * σ.n + 2 ≤ B)
    (hK : ∀ j, j < σ.n → DblAt x σ.p (Nat.bits j) →
      PS x B tg { σ with s := j, p := σ.p + 2 * (Nat.bits j).length + 2, tmp := 0 } (K j)) :
    PS x B sg σ (∃ j, j < σ.n ∧ DblAt x σ.p (Nat.bits j) ∧ K j) := by
  refine (nsem_guess pathA pathOr x B 4 1 (by decide) sg sc sm scp rej rfl rfl rfl rfl
    (fun j => DblAt x σ.p (Nat.bits j) ∧ K j) σ.v (PReg.reg hσ none none)
    (by simp only [PReg.v_4, PReg.v_1]; omega) (fun j hj1 hj2 => ?_)).congr ?_
  · simp only [PReg.v_4, PReg.v_1] at hj1 hj2
    pw_regs
    have hjb := length_bits_le_self j
    refine nsem_copy pathA pathOr x B 6 4 (by decide) scp sbp stt rfl rfl _ _
      (PReg.reg (by pw_le) none none) (by simp; omega) ?_
    pw_regs
    refine ps_scmp _ _ (by pw_le) (by simp; omega) fun hd => ?_
    simp only at hd ⊢
    exact PS.of_eq (by ext <;> simp) (hK j hj2 hd)
  · simp only [PReg.v_4, PReg.v_1, hs]
    exact ⟨fun ⟨j, _, h⟩ => ⟨j, h⟩, fun ⟨j, h⟩ => ⟨j, Nat.zero_le _, h⟩⟩

/-- **The matrix scan**: from pair `i ≤ n²` with row `i / n` and column `i % n`, some branch
accepts iff the matrix field is well formed from pair `i` on and the continuation accepts.

**Proof sketch.** Induction on `n² - i`. A pointer outside the input rejects (and the
field cannot be well formed); a data pair before pair `n²` advances the column (and the
row at the end of a row); a separator is accepted exactly at pair `n²`. -/
lemma ps_mat (hB : 2 * x.length + 2 ≤ B) (K : Prop) (i : ℕ) (σ : PReg) (hσ : σ.Le B)
    (hn : σ.n ≤ x.length) (hp : σ.p = 2 * σ.n + 2 + 2 * i) (ha : σ.a = i / σ.n)
    (hb : σ.b = i % σ.n) (hi : i ≤ σ.n * σ.n)
    (hK : x.getD (2 * σ.n + 2 + 2 * (σ.n * σ.n) + 1) false = true →
      PS x B sg { σ with p := 2 * σ.n + 2 + 2 * (σ.n * σ.n) + 2, a := σ.n, b := 0 } K) :
    PS x B m0 σ (MatRest x σ.n i ∧ K) := by
  suffices H : ∀ d i (σ : PReg), σ.n * σ.n - i = d → σ.Le B → σ.n ≤ x.length →
      σ.p = 2 * σ.n + 2 + 2 * i → σ.a = i / σ.n → σ.b = i % σ.n → i ≤ σ.n * σ.n →
      (x.getD (2 * σ.n + 2 + 2 * (σ.n * σ.n) + 1) false = true →
        PS x B sg { σ with p := 2 * σ.n + 2 + 2 * (σ.n * σ.n) + 2, a := σ.n, b := 0 } K) →
      PS x B m0 σ (MatRest x σ.n i ∧ K) from H _ i σ rfl hσ hn hp ha hb hi hK
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro i σ hd hσ hn hp ha hb hi hK
  have ha' : σ.a ≤ σ.n := by rw [ha]; exact Nat.div_le_of_le_mul hi
  have hlastiff : σ.a = σ.n ↔ i = σ.n * σ.n := by rw [ha]; exact div_eq_self_iff hi
  -- a data pair (equal bits) at `p, p + 1`, the pointer on its second bit
  have hdata : σ.p < x.length → x.getD σ.p false = x.getD (σ.p + 1) false →
      PS x B m5 { σ with p := σ.p + 1 } (MatRest x σ.n i ∧ K) := by
    intro hpx heq
    by_cases hlast : i = σ.n * σ.n
    · refine (NSem.jeq_pos rfl (PReg.reg (by pw_le) _ _) (by simpa using hlastiff.mpr hlast)
        (NSem.ret rfl (PReg.reg (by pw_le) _ _))).congr ?_
      simp only [Bool.false_eq_true, false_iff, not_and]
      intro hM _
      have h1 := hM.2.1; have h2 := hM.2.2
      rw [← hlast, ← hp] at h1
      rw [← hlast, ← hp] at h2
      rw [← heq, h1] at h2; exact absurd h2 (by simp)
    · have hlt : i < σ.n * σ.n := by omega
      have hpos : 0 < σ.n := by
        rcases Nat.eq_zero_or_pos σ.n with h | h
        · rw [h] at hlt; simp at hlt
        · exact h
      have hmod := Nat.mod_lt i hpos
      have hdiv : i / σ.n < σ.n := by
        rcases Nat.lt_or_ge (i / σ.n) σ.n with h | h
        · exact h
        · exfalso; have := (hlastiff.mp (by omega)); omega
      refine NSem.jeq_neg rfl (PReg.reg (by pw_le) _ _) (by simp only [PReg.v_1, PReg.v_2]; omega) ?_
      refine NSem.inc rfl (PReg.reg (by pw_le) _ _) ?_
      pw_regs
      refine NSem.inc rfl (PReg.reg (by pw_le) _ _) ?_
      pw_regs
      have hrec : ∀ a' b', a' = (i + 1) / σ.n → b' = (i + 1) % σ.n →
          PS x B m0 { σ with p := σ.p + 2, a := a', b := b' } (MatRest x σ.n i ∧ K) := by
        intro a' b' e3 e4
        have ha2 : a' ≤ σ.n := by
          rw [e3]; exact Nat.div_le_of_le_mul (by omega)
        have hb2 : b' < σ.n := by rw [e4]; exact Nat.mod_lt _ hpos
        have := ih (σ.n * σ.n - (i + 1)) (by omega) (i + 1) { σ with p := σ.p + 2, a := a', b := b' }
          rfl (by pw_le) hn (by dsimp only; omega) e3 e4 (by dsimp only; omega) hK
        refine this.congr ⟨fun ⟨hM, hk⟩ => ⟨⟨fun j hj1 hj2 => ?_, hM.2⟩, hk⟩,
          fun ⟨hM, hk⟩ => ⟨⟨fun j hj1 hj2 => hM.1 j (by omega) hj2, hM.2⟩, hk⟩⟩
        rcases Nat.eq_or_lt_of_le hj1 with h | h
        · subst h; rw [show 2 * σ.n + 2 + 2 * i = σ.p by omega]; exact heq
        · exact hM.1 j (by omega) hj2
      have hds := divmod_succ (i := i) hpos
      by_cases hc : i % σ.n + 1 = σ.n
      · refine NSem.jeq_pos rfl (PReg.reg (by pw_le) _ _) (by simp; omega) ?_
        refine NSem.clr rfl (PReg.reg (by pw_le) _ _) ?_
        pw_regs
        refine NSem.inc rfl (PReg.reg (by pw_le) _ _) ?_
        pw_regs
        exact PS.of_eq (by pw_ext')
          (hrec (i / σ.n + 1) 0 (hds.1 hc).1.symm (hds.1 hc).2.symm)
      · refine NSem.jeq_neg rfl (PReg.reg (by pw_le) _ _) (by simp; omega) ?_
        exact PS.of_eq (by ext <;> simp <;> omega)
          (hrec (i / σ.n) (i % σ.n + 1) (hds.2 hc).1.symm (hds.2 hc).2.symm)
  by_cases hpx : σ.p < x.length
  · refine NSem.call_pos rfl (PReg.reg hσ _ _)
      (by simp only [PReg.v_0, pathOr_len, decide_eq_true_eq]; exact hpx) ?_
    cases hb0 : x.getD σ.p false
    · refine NSem.call_neg rfl (PReg.reg hσ _ _) (by simp only [PReg.v_0, pathOr_bit, hb0]) ?_
      refine NSem.inc rfl (PReg.reg (by pw_le) _ _) ?_
      pw_regs
      cases hb1 : x.getD (σ.p + 1) false
      · refine NSem.call_neg rfl (PReg.reg (by pw_le) _ _)
          (by simp only [PReg.v_0, pathOr_bit, hb1]) ?_
        exact hdata hpx (by rw [hb0, hb1])
      · refine NSem.call_pos rfl (PReg.reg (by pw_le) _ _)
          (by simp only [PReg.v_0, pathOr_bit, hb1]) ?_
        by_cases hlast : i = σ.n * σ.n
        · refine NSem.jeq_pos rfl (PReg.reg (by pw_le) _ _) (by simpa using hlastiff.mpr hlast) ?_
          refine NSem.inc rfl (PReg.reg (by pw_le) _ _) ?_
          pw_regs
          have hx1 : x.getD (2 * σ.n + 2 + 2 * (σ.n * σ.n) + 1) false = true := by
            rw [← hlast, ← hp]; exact hb1
          have hb00 : σ.b = 0 := by rw [hb, hlast, Nat.mul_mod_left]
          have haa : σ.a = σ.n := hlastiff.mpr hlast
          refine PS.of_eq (by ext <;> simp <;> omega) ((hK hx1).congr ⟨fun hk => ⟨⟨fun j hj1 hj2 =>
            absurd hj2 (by omega), by rw [← hlast, ← hp]; exact hb0, hx1⟩, hk⟩, fun h => h.2⟩)
        · refine (NSem.jeq_neg rfl (PReg.reg (by pw_le) _ _)
            (by simp; exact fun h => hlast (hlastiff.mp h)) (NSem.ret rfl (PReg.reg (by pw_le) _ _))).congr ?_
          simp only [Bool.false_eq_true, false_iff, not_and]
          intro hM _
          have := hM.1 i le_rfl (by omega)
          rw [← hp, hb0, hb1] at this; exact absurd this (by simp)
    · refine NSem.call_pos rfl (PReg.reg hσ _ _) (by simp only [PReg.v_0, pathOr_bit, hb0]) ?_
      refine NSem.inc rfl (PReg.reg (by pw_le) _ _) ?_
      pw_regs
      cases hb1 : x.getD (σ.p + 1) false
      · refine (NSem.call_neg rfl (PReg.reg (by pw_le) _ _)
          (by simp only [PReg.v_0, pathOr_bit, hb1]) (NSem.ret rfl (PReg.reg (by pw_le) _ _))).congr ?_
        simp only [Bool.false_eq_true, false_iff, not_and]
        intro hM _
        by_cases hlast : i = σ.n * σ.n
        · have := hM.2.1; rw [← hlast, ← hp, hb0] at this; exact absurd this (by simp)
        · have := hM.1 i le_rfl (by omega)
          rw [← hp, hb0, hb1] at this; exact absurd this (by simp)
      · refine NSem.call_pos rfl (PReg.reg (by pw_le) _ _)
          (by simp only [PReg.v_0, pathOr_bit, hb1]) ?_
        exact hdata hpx (by rw [hb0, hb1])
  · refine (NSem.call_neg rfl (PReg.reg hσ _ _)
      (by simp only [PReg.v_0, pathOr_len, decide_eq_false_iff_not]; exact hpx)
      (NSem.ret rfl (PReg.reg hσ _ _))).congr ?_
    simp only [Bool.false_eq_true, false_iff, not_and]
    intro hM _
    have := lt_of_getD_true hM.2.2
    omega

/-- **The unary scan**: from pair `k = n` (the count so far), some branch accepts iff the
unary prefix ends at some pair `n' ≥ k` and the continuation accepts with `n'`.

**Proof sketch.** Induction on `|x| - p`. The aligned pair at `p = 2k` is read: `11` counts
one more and recurs (the pointer stays inside the input), `01` ends the prefix with
`n' = k`, and `00` or `10` rejects — and then no `n' ≥ k` can end the prefix, as the pair
at `k` is neither `11` nor `01`. -/
lemma ps_unary (hB : 2 * x.length + 2 ≤ B) (K : ℕ → Prop) (σ : PReg) (hσ : σ.Le B)
    (hp : σ.p = 2 * σ.n) (hpx : σ.p ≤ x.length)
    (hK : ∀ n', σ.n ≤ n' → UnaryRest x σ.n n' →
      PS x B m0 { σ with p := 2 * n' + 2, n := n' } (K n')) :
    PS x B u0 σ (∃ n', σ.n ≤ n' ∧ UnaryRest x σ.n n' ∧ K n') := by
  suffices H : ∀ d (σ : PReg), x.length - σ.p = d → σ.Le B → σ.p = 2 * σ.n →
      σ.p ≤ x.length → (∀ n', σ.n ≤ n' → UnaryRest x σ.n n' →
        PS x B m0 { σ with p := 2 * n' + 2, n := n' } (K n')) →
      PS x B u0 σ (∃ n', σ.n ≤ n' ∧ UnaryRest x σ.n n' ∧ K n') from
    H _ σ rfl hσ hp hpx hK
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro σ hd hσ hp hpx hK
  have hb0' : ∀ b, x.getD σ.p false = b → x.getD (2 * σ.n) false = b := fun b h => hp ▸ h
  have hb1' : ∀ b, x.getD (σ.p + 1) false = b → x.getD (2 * σ.n + 1) false = b :=
    fun b h => hp ▸ h
  cases hb0 : x.getD σ.p false
  · refine NSem.call_neg rfl (PReg.reg hσ _ _) (by simp only [PReg.v_0, pathOr_bit, hb0]) ?_
    refine NSem.inc rfl (PReg.reg hσ _ _) ?_
    pw_regs
    cases hb1 : x.getD (σ.p + 1) false
    · refine (NSem.call_neg rfl (PReg.reg (by pw_le) _ _) (by simp only [PReg.v_0, pathOr_bit, hb1])
        (NSem.ret rfl (PReg.reg (by pw_le) _ _))).congr ?_
      simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
      intro n' hn' hU _
      rcases Nat.eq_or_lt_of_le hn' with h | h
      · subst h; have := hU.2.2; rw [hb1' false hb1] at this; exact absurd this (by simp)
      · have := (hU.1 σ.n le_rfl h).1; rw [hb0' false hb0] at this; exact absurd this (by simp)
    · have hlt : σ.p + 1 < x.length := lt_of_getD_true hb1
      refine NSem.call_pos rfl (PReg.reg (by pw_le) _ _) (by simp only [PReg.v_0, pathOr_bit, hb1]) ?_
      refine NSem.inc rfl (PReg.reg (by pw_le) _ _) ?_
      pw_regs
      have hU : UnaryRest x σ.n σ.n :=
        ⟨fun i h1 h2 => absurd h2 (by omega), hb0' _ hb0, hb1' _ hb1⟩
      refine PS.of_eq (σ' := { σ with p := 2 * σ.n + 2, n := σ.n }) (by pw_ext) ?_
      refine (hK σ.n le_rfl hU).congr ⟨fun h => ⟨σ.n, le_rfl, hU, h⟩, ?_⟩
      rintro ⟨n', hn', hU', hk⟩
      rcases Nat.eq_or_lt_of_le hn' with h | h
      · subst h; exact hk
      · exfalso; have := (hU'.1 σ.n le_rfl h).1; rw [hb0' _ hb0] at this; simp at this
  · have hlt0 : σ.p < x.length := lt_of_getD_true hb0
    refine NSem.call_pos rfl (PReg.reg hσ _ _) (by simp only [PReg.v_0, pathOr_bit, hb0]) ?_
    refine NSem.inc rfl (PReg.reg hσ _ _) ?_
    pw_regs
    cases hb1 : x.getD (σ.p + 1) false
    · refine (NSem.call_neg rfl (PReg.reg (by pw_le) _ _) (by simp only [PReg.v_0, pathOr_bit, hb1])
        (NSem.ret rfl (PReg.reg (by pw_le) _ _))).congr ?_
      simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
      intro n' hn' hU _
      rcases Nat.eq_or_lt_of_le hn' with h | h
      · subst h; have := hU.2.1; rw [hb0' true hb0] at this; exact absurd this (by simp)
      · have := (hU.1 σ.n le_rfl h).2; rw [hb1' false hb1] at this; exact absurd this (by simp)
    · have hlt : σ.p + 1 < x.length := lt_of_getD_true hb1
      refine NSem.call_pos rfl (PReg.reg (by pw_le) _ _) (by simp only [PReg.v_0, pathOr_bit, hb1]) ?_
      refine NSem.inc rfl (PReg.reg (by pw_le) _ _) ?_
      pw_regs
      refine NSem.inc rfl (PReg.reg (by pw_le) _ _) ?_
      pw_regs
      let σ₁ : PReg := { σ with p := σ.p + 2, n := σ.n + 1 }
      refine PS.of_eq (σ' := σ₁) (by pw_ext) ?_
      have hrec := ih (x.length - σ₁.p) (by dsimp only [σ₁]; omega) σ₁ rfl (by simp only [PReg.Le, σ₁] at hσ ⊢; omega)
        (by dsimp only [σ₁]; omega) (by dsimp only [σ₁]; omega) (fun n' h1 h2 => by
          refine hK n' (by dsimp only [σ₁] at h1; omega) ⟨fun i hi1 hi2 => ?_, h2.2⟩
          rcases Nat.eq_or_lt_of_le hi1 with h | h
          · subst h; exact ⟨hb0' _ hb0, hb1' _ hb1⟩
          · exact h2.1 i (by dsimp only [σ₁]; omega) hi2)
      refine hrec.congr ⟨fun ⟨n', h1, h2, h3⟩ => ⟨n', by dsimp only [σ₁] at h1; omega,
        ⟨fun i hi1 hi2 => ?_, h2.2⟩, h3⟩, fun ⟨n', h1, h2, h3⟩ => ⟨n', ?_, ⟨fun i hi1 hi2 =>
          h2.1 i (by dsimp only [σ₁] at hi1; omega) hi2, h2.2⟩, h3⟩⟩
      · rcases Nat.eq_or_lt_of_le hi1 with h | h
        · subst h; exact ⟨hb0' _ hb0, hb1' _ hb1⟩
        · exact h2.1 i (by dsimp only [σ₁]; omega) hi2
      · dsimp only [σ₁]
        rcases Nat.eq_or_lt_of_le h1 with h | h
        · exfalso; subst h; have := h2.2.1; rw [hb0' _ hb0] at this; simp at this
        · omega

/-- The register file at the start: all registers `0`. -/
def PReg.zero : PReg := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- **The semantics of the walk machine**: every branch terminates with registers at most
`4 (|x| + 1)`, and some branch accepts iff `PathAcc x`.

**Proof sketch.** Compose the phase lemmas from the start: `ps_unary`, `ps_mat`,
`ps_sphase`, `ps_tphase`, `ps_walk`; the register bounds come from the facts checked so far
(the separators lie inside the input). -/
theorem ps_start (x : List Bool) : PS x (4 * (x.length + 1)) u0 PReg.zero (PathAcc x) := by
  have hB : 2 * x.length + 2 ≤ 4 * (x.length + 1) := by omega
  refine (ps_unary hB (fun n => MatRest x n 0 ∧
      ∃ s, s < n ∧ DblAt x (2 * n + 2 + 2 * (n * n) + 2) (Nat.bits s) ∧
        ∃ t, t < n ∧
          PlainAt x (2 * n + 2 + 2 * (n * n) + 2 + 2 * (Nat.bits s).length + 2) (Nat.bits t) ∧
          WalkLe (pathEdge x n) n n s t) PReg.zero (by simp only [PReg.zero, PReg.Le]; omega)
      rfl (by simp [PReg.zero]) ?_).congr ?_
  · intro n _ hU
    simp only [PReg.zero] at hU
    have hn1 := lt_of_getD_true hU.2.2
    refine ps_mat hB _ 0 _ (by simp only [PReg.zero, PReg.Le]; omega) (by dsimp only; omega)
      (by simp) (by simp [PReg.zero]) (by simp [PReg.zero]) (by simp) ?_
    intro hm1
    simp only at hm1
    have hm := lt_of_getD_true hm1
    refine ps_sphase _ _ (by simp only [PReg.zero, PReg.Le]; omega) rfl rfl
      (by dsimp only; omega) ?_
    intro j hj hD
    simp only at hj hD
    have hr := lt_of_getD_true hD.2.2
    have hjb := length_bits_le_self j
    refine ps_tphase hB _ _ (by simp only [PReg.zero, PReg.Le]; omega) rfl rfl
      (by dsimp only; omega) (by dsimp only; omega) ?_
    intro t ht _
    simp only at ht
    exact (ps_walk hB _ (by simp only [PReg.zero, PReg.Le]; omega) (by dsimp only; omega)
      (by dsimp only; omega) (by dsimp only [PReg.zero]; omega) (by dsimp only; omega)).congr
      (by simp [PReg.zero])
  · simp only [PathAcc, PReg.zero, Nat.zero_le, true_and]

end LogProg

/-- **The raw `PATH` language is in `NL`** [AB09, §4.1.2]: the walk machine decides it with
registers of at most `4 (|x| + 1)`.

**Proof sketch.** `narm_decides_poly` with the input-access deciders (`pathAs_mem`): the
uniform halting bound and the accepting branches come from `ps_start` by `NSem.decides`, the
syntactic preconditions from `pathA_npreS`, and acceptance is membership by
`pathAcc_iff`. -/
theorem pathRawLang_mem_NL : pathRawLang ∈ NL := by
  refine LogProg.narm_decides_poly LogProg.pathA LogProg.PathLabel.u0 LogProg.pathAs
    LogProg.pathAs_mem 4 1 fun x => ?_
  obtain ⟨N, hN, hiff⟩ := (LogProg.ps_start x).decides
  have h0 : LogProg.PReg.zero.v = fun _ => 0 := by funext r; fin_cases r <;> rfl
  rw [h0] at hN hiff
  refine ⟨N, hN.mono fun a ha => ⟨LogProg.pathA_npreS x a, fun r => by simpa using ha r⟩, ?_⟩
  rw [← pathAcc_iff]
  exact hiff

end Complexity
