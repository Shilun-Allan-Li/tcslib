/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.UPathParse

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The deterministic checks of the random-walk machine: source and target

[AB09, Theorem 7.19]: a randomized logspace machine may not guess the endpoints, as the
walk machine of `PATH ∈ NL` does (`Complexity.LogProg.ps_sphase`): a guess would cost
probability. `Complexity.LogProg.upA` finds them deterministically instead, comparing
`bits c` with the endpoint field for `c = 0, 1, …` below `n` and restarting at a saved
position after each mismatch. The comparisons follow `Complexity.LogProg.ps_scmp` and
`Complexity.LogProg.ps_tcmp`, with a mismatch continuing the search instead of rejecting.

## Main definitions

None: the results are phase lemmas about `Complexity.LogProg.upA`.

## Main results

* `Complexity.LogProg.ups_scmp`, `Complexity.LogProg.ups_ssearch` — the source.
* `Complexity.LogProg.ups_tcmp`, `Complexity.LogProg.ups_tsearch` — the target.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.7.)
-/

namespace Complexity.LogProg

open Turing ULabel UPathTac

variable {x : List Bool} {B : ℕ}

/-- **The source comparison**: the binary digits of the scratch copy are compared with the
doubled field at the pointer, followed by the separator; a match continues to the copy into
the current vertex, a mismatch to the next candidate.

**Proof sketch.** Strong induction on the copy `w`, as `Complexity.LogProg.ps_scmp`: at
`w = 0` the next aligned pair must be the separator `01`; otherwise both bits of the next
pair must be the parity of `w` (`bits_eq_cons`, `dblAt_cons`) and the comparison recurs on
`w / 2` two positions later. -/
lemma ups_scmp (q : ℚ) : ∀ w (σ : UReg), σ.tmp = w → σ.Le B →
    σ.p + 2 * (Nat.bits σ.tmp).length + 2 ≤ B →
    (DblAt x σ.p (Nat.bits σ.tmp) →
      UPS x B (cp .sCur) { σ with p := σ.p + 2 * (Nat.bits σ.tmp).length + 2, tmp := 0 } q) →
    (¬ DblAt x σ.p (Nat.bits σ.tmp) → ∀ p tmp, p ≤ B → tmp ≤ B →
      UPS x B s6 { σ with p := p, tmp := tmp } q) →
    UPS x B stt σ q := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro σ hw hσ hp hK hM
  rcases Nat.eq_zero_or_pos w with rfl | hwpos
  · simp only [hw, Nat.zero_bits] at hp hK hM
    refine PSem.jz_pos rfl (UReg.reg hσ _ _) (by simpa using hw) ?_
    have hD : ∀ (b0 b1 : Bool), x.getD σ.p false = b0 → x.getD (σ.p + 1) false = b1 →
        (DblAt x σ.p [] ↔ b0 = false ∧ b1 = true) := by
      intro b0 b1 h0 h1
      simp only [DblAt, List.length_nil, Nat.mul_zero, Nat.add_zero, h0, h1]
      simp
    have hmis : ¬ DblAt x σ.p [] → ∀ p, p ≤ B → UPS x B s6 { σ with p := p } q :=
      fun h p hp => UPS.of_eq (by uw_ext) (hM h p σ.tmp hp (by uw_le))
    cases hb0 : x.getD σ.p false
    · refine PSem.call_neg rfl (UReg.reg hσ _ _) (by simp only [UReg.v_0, pathOr_bit, hb0]) ?_
      refine PSem.inc rfl (UReg.reg (by uw_le) _ _) ?_
      uw_regs
      cases hb1 : x.getD (σ.p + 1) false
      · refine PSem.call_neg rfl (UReg.reg (by uw_le) _ _)
          (by simp only [UReg.v_0, pathOr_bit, hb1]) ?_
        exact hmis (by rw [hD _ _ hb0 hb1]; simp) _ (by omega)
      · refine PSem.call_pos rfl (UReg.reg (by uw_le) _ _)
          (by simp only [UReg.v_0, pathOr_bit, hb1]) ?_
        refine PSem.inc rfl (UReg.reg (by uw_le) _ _) ?_
        uw_regs
        exact UPS.of_eq (by uw_ext) (hK ((hD _ _ hb0 hb1).mpr ⟨rfl, rfl⟩))
    · refine PSem.call_pos rfl (UReg.reg hσ _ _) (by simp only [UReg.v_0, pathOr_bit, hb0]) ?_
      exact UPS.of_eq (by uw_ext) (hmis (by rw [hD _ _ hb0 rfl]; simp) σ.p hσ.1)
  · have hw0 : w ≠ 0 := by omega
    have hbits := bits_eq_cons hw0
    rw [hw, hbits] at hp hK hM
    simp only [List.length_cons] at hp hK hM
    refine PSem.jz_neg rfl (UReg.reg hσ _ _) (by simp only [UReg.v_6]; omega) ?_
    have hmis : ¬ DblAt x σ.p (decide (w % 2 = 1) :: Nat.bits (w / 2)) → ∀ p, p ≤ B →
        UPS x B s6 { σ with p := p } q :=
      fun h p hp => UPS.of_eq (by uw_ext) (hM h p σ.tmp hp (by uw_le))
    -- the rest of the field, after one checked doubled bit
    have hnext : ∀ b : Bool, b = decide (w % 2 = 1) → x.getD σ.p false = b →
        x.getD (σ.p + 1) false = b → UPS x B sad { σ with p := σ.p + 1 } q := by
      intro b hb h0 h1
      refine PSem.inc rfl (UReg.reg (by uw_le) _ _) ?_
      uw_regs
      refine PSem.half rfl (UReg.reg (by uw_le) _ _) ?_
      uw_regs
      refine UPS.of_eq (σ' := { σ with p := σ.p + 1 + 1, tmp := w / 2 }) (by uw_ext) ?_
      refine ih (w / 2) (by omega) _ rfl (by uw_le) (by dsimp only; omega) (fun hd => ?_)
        (fun hd p' t' hp' ht' => ?_)
      · refine UPS.of_eq (by uw_ext) (hK ?_)
        rw [dblAt_cons]; exact ⟨⟨hb ▸ h0, hb ▸ h1⟩, hd⟩
      · refine UPS.of_eq (by uw_ext) (hM ?_ p' t' hp' ht')
        rw [dblAt_cons]; exact fun h => hd h.2
    have hbad : ∀ b : Bool, x.getD σ.p false ≠ b ∨ x.getD (σ.p + 1) false ≠ b →
        b = decide (w % 2 = 1) → ¬ DblAt x σ.p (decide (w % 2 = 1) :: Nat.bits (w / 2)) := by
      intro b h hb hD
      rw [dblAt_cons, ← hb] at hD
      rcases h with h | h
      · exact h hD.1.1
      · exact h hD.1.2
    by_cases hodd : w % 2 = 1
    · refine PSem.jodd_pos rfl (UReg.reg hσ _ _) (by simp only [UReg.v_6, hw]; exact hodd) ?_
      cases hb0 : x.getD σ.p false
      · refine PSem.call_neg rfl (UReg.reg hσ _ _) (by simp only [UReg.v_0, pathOr_bit, hb0]) ?_
        exact UPS.of_eq (by uw_ext) (hmis (hbad true (Or.inl (by rw [hb0]; decide))
          (by simp [hodd])) σ.p hσ.1)
      · refine PSem.call_pos rfl (UReg.reg hσ _ _) (by simp only [UReg.v_0, pathOr_bit, hb0]) ?_
        refine PSem.inc rfl (UReg.reg (by uw_le) _ _) ?_
        uw_regs
        cases hb1 : x.getD (σ.p + 1) false
        · refine PSem.call_neg rfl (UReg.reg (by uw_le) _ _)
            (by simp only [UReg.v_0, pathOr_bit, hb1]) ?_
          exact hmis (hbad true (Or.inr (by rw [hb1]; decide)) (by simp [hodd])) _ (by omega)
        · refine PSem.call_pos rfl (UReg.reg (by uw_le) _ _)
            (by simp only [UReg.v_0, pathOr_bit, hb1]) ?_
          exact hnext true (by simp [hodd]) hb0 hb1
    · refine PSem.jodd_neg rfl (UReg.reg hσ _ _) (by simp only [UReg.v_6, hw]; exact hodd) ?_
      cases hb0 : x.getD σ.p false
      · refine PSem.call_neg rfl (UReg.reg hσ _ _) (by simp only [UReg.v_0, pathOr_bit, hb0]) ?_
        refine PSem.inc rfl (UReg.reg (by uw_le) _ _) ?_
        uw_regs
        cases hb1 : x.getD (σ.p + 1) false
        · refine PSem.call_neg rfl (UReg.reg (by uw_le) _ _)
            (by simp only [UReg.v_0, pathOr_bit, hb1]) ?_
          exact hnext false (by simp [hodd]) hb0 hb1
        · refine PSem.call_pos rfl (UReg.reg (by uw_le) _ _)
            (by simp only [UReg.v_0, pathOr_bit, hb1]) ?_
          exact hmis (hbad false (Or.inr (by rw [hb1]; decide)) (by simp [hodd])) _ (by omega)
      · refine PSem.call_pos rfl (UReg.reg hσ _ _) (by simp only [UReg.v_0, pathOr_bit, hb0]) ?_
        exact UPS.of_eq (by uw_ext) (hmis (hbad false (Or.inl (by rw [hb0]; decide))
          (by simp [hodd])) σ.p hσ.1)

/-- **The target comparison**: the binary digits of the scratch copy are compared with the
input suffix from the pointer, which must end the input; a match continues to the copy into
the target, a mismatch to the next candidate.

**Proof sketch.** Strong induction on the copy `w`, as `Complexity.LogProg.ps_tcmp`: at
`w = 0` the length query must find the end of the input; otherwise the pointer must be inside
the input, the bit under it the parity of `w` (`plainAt_cons`), and the comparison recurs on
`w / 2` one position later. -/
lemma ups_tcmp (q : ℚ) : ∀ w (σ : UReg), σ.tmp = w → σ.Le B → 2 * x.length + 2 ≤ B →
    σ.p ≤ x.length →
    (PlainAt x σ.p (Nat.bits σ.tmp) →
      UPS x B (cp .tT) { σ with p := x.length, tmp := 0 } q) →
    (¬ PlainAt x σ.p (Nat.bits σ.tmp) → ∀ p tmp, p ≤ B → tmp ≤ B →
      UPS x B t6 { σ with p := p, tmp := tmp } q) →
    UPS x B ttt σ q := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro σ hw hσ hB hp hK hM
  have hmis : ¬ PlainAt x σ.p (Nat.bits σ.tmp) → UPS x B t6 σ q :=
    fun h => UPS.of_eq (by uw_ext) (hM h σ.p σ.tmp hσ.1 (by uw_le))
  rcases Nat.eq_zero_or_pos w with rfl | hwpos
  · refine PSem.jz_pos rfl (UReg.reg hσ _ _) (by simpa using hw) ?_
    simp only [hw, Nat.zero_bits] at hK hmis
    by_cases hpx : σ.p < x.length
    · refine PSem.call_pos rfl (UReg.reg hσ _ _)
        (by simp only [UReg.v_0, pathOr_len, decide_eq_true_eq]; exact hpx) (hmis ?_)
      intro h; have := h.2; simp only [List.length_nil] at this; omega
    · have hd : PlainAt x σ.p [] := ⟨fun i hi => absurd hi (by simp), by simp; omega⟩
      refine PSem.call_neg rfl (UReg.reg hσ _ _)
        (by simp only [UReg.v_0, pathOr_len, decide_eq_false_iff_not]; exact hpx) ?_
      exact UPS.of_eq (by uw_ext) (hK hd)
  · have hw0 : w ≠ 0 := by omega
    have hbits := bits_eq_cons hw0
    rw [hw, hbits] at hK hM hmis
    refine PSem.jz_neg rfl (UReg.reg hσ _ _) (by simp only [UReg.v_6]; omega) ?_
    by_cases hpx : σ.p < x.length
    · refine PSem.call_pos rfl (UReg.reg hσ _ _)
        (by simp only [UReg.v_0, pathOr_len, decide_eq_true_eq]; exact hpx) ?_
      have hnext : ∀ b : Bool, b = decide (w % 2 = 1) → x.getD σ.p false = b →
          UPS x B tad σ q := by
        intro b hb h0
        refine PSem.inc rfl (UReg.reg hσ _ _) ?_
        uw_regs
        refine PSem.half rfl (UReg.reg (by uw_le) _ _) ?_
        uw_regs
        refine UPS.of_eq (σ' := { σ with p := σ.p + 1, tmp := w / 2 }) (by uw_ext) ?_
        refine ih (w / 2) (by omega) _ rfl (by uw_le) hB (by dsimp only; omega)
          (fun hd => ?_) (fun hd p' t' hp' ht' => ?_)
        · refine UPS.of_eq (by uw_ext) (hK ?_)
          rw [plainAt_cons]; exact ⟨hb ▸ h0, hd⟩
        · refine UPS.of_eq (by uw_ext) (hM ?_ p' t' hp' ht')
          rw [plainAt_cons]; exact fun h => hd h.2
      have hbad : ∀ b : Bool, b ≠ decide (w % 2 = 1) → x.getD σ.p false = b →
          ¬ PlainAt x σ.p (decide (w % 2 = 1) :: Nat.bits (w / 2)) := by
        intro b hb h0 hP
        rw [plainAt_cons, h0] at hP
        exact hb hP.1
      by_cases hodd : w % 2 = 1
      · refine PSem.jodd_pos rfl (UReg.reg hσ _ _) (by simp only [UReg.v_6, hw]; exact hodd) ?_
        cases hb0 : x.getD σ.p false
        · exact PSem.call_neg rfl (UReg.reg hσ _ _) (by simp only [UReg.v_0, pathOr_bit, hb0])
            (hmis (hbad false (by simp [hodd]) hb0))
        · refine PSem.call_pos rfl (UReg.reg hσ _ _) (by simp only [UReg.v_0, pathOr_bit, hb0]) ?_
          exact hnext true (by simp [hodd]) hb0
      · refine PSem.jodd_neg rfl (UReg.reg hσ _ _) (by simp only [UReg.v_6, hw]; exact hodd) ?_
        cases hb0 : x.getD σ.p false
        · refine PSem.call_neg rfl (UReg.reg hσ _ _) (by simp only [UReg.v_0, pathOr_bit, hb0]) ?_
          exact hnext false (by simp [hodd]) hb0
        · exact PSem.call_pos rfl (UReg.reg hσ _ _) (by simp only [UReg.v_0, pathOr_bit, hb0])
            (hmis (hbad true (by simp [hodd]) hb0))
    · refine PSem.call_neg rfl (UReg.reg hσ _ _)
        (by simp only [UReg.v_0, pathOr_len, decide_eq_false_iff_not]; exact hpx) (hmis ?_)
      intro h
      have := h.2
      simp only [List.length_cons] at this
      omega

/-- **The source search**: from the candidate `u ≤ n`, if some `j ∈ [u, n)` has `bits j` in
the doubled field at the saved position `q`, the machine continues with the least such `j`
as current vertex; if none has, it rejects.

**Proof sketch.** Induction on `n - u`: reject at `u = n`; otherwise copy `u` into the
scratch register, reset the pointer to `q`, compare (`ups_scmp`), and on a mismatch try
`u + 1`. -/
lemma ups_ssearch (q : ℚ) : ∀ dd (σ : UReg), σ.n - σ.u = dd → σ.Le B → σ.u ≤ σ.n →
    σ.cur = 0 → σ.q + 2 * σ.n + 2 ≤ B →
    (∀ j, σ.u ≤ j → j < σ.n → DblAt x σ.q (Nat.bits j) →
      UPS x B t0 { σ with
        u := j, cur := j, p := σ.q + 2 * (Nat.bits j).length + 2, tmp := 0 } q) →
    ((¬ ∃ j, σ.u ≤ j ∧ j < σ.n ∧ DblAt x σ.q (Nat.bits j)) → q = 0) →
    UPS x B s1 σ q := by
  intro dd
  induction dd with
  | zero =>
    intro σ hd hσ hu _ _ _ h0
    refine PSem.jeq_pos rfl (UReg.reg hσ _ _) (by simp; omega) (ups_rej hσ (h0 ?_))
    rintro ⟨j, h1, h2, -⟩; omega
  | succ dd ih =>
    intro σ hd hσ hu hc hq hK h0
    have hu1 : σ.u + 1 ≤ σ.n := by omega
    have hd1 : σ.n - (σ.u + 1) = dd := by rw [Nat.sub_add_eq, hd, Nat.add_sub_cancel]
    have hjb := length_bits_le_self σ.u
    refine PSem.jeq_neg rfl (UReg.reg hσ _ _) (by simp; omega) ?_
    refine PSem.clr rfl (UReg.reg hσ _ _) ?_
    uw_regs
    refine ups_cp .sTmp q _ (by uw_le) (by simp [cpDst, cpSrc]) ?_
    simp only [cpDst, cpSrc, cpEx]
    uw_regs
    refine PSem.clr rfl (UReg.reg (by uw_le) _ _) ?_
    uw_regs
    refine ups_cp .sP q _ (by uw_le) (by simp [cpDst, cpSrc]) ?_
    simp only [cpDst, cpSrc, cpEx]
    uw_regs
    refine ups_scmp q _ _ rfl (by uw_le) (by dsimp only; omega) (fun hD => ?_)
      (fun hD p' t' hp' ht' => ?_)
    · simp only at hD ⊢
      refine ups_cp .sCur q _ (by uw_le) (by simp [cpDst, cpSrc, hc]) ?_
      simp only [cpDst, cpSrc, cpEx]
      uw_regs
      exact UPS.of_eq (by uw_ext) (hK σ.u le_rfl (by omega) hD)
    · simp only at hD ⊢
      refine PSem.inc rfl (UReg.reg (by uw_le) _ _) ?_
      uw_regs
      refine ih { σ with p := p', tmp := t', u := σ.u + 1 }
        hd1 (by uw_le)
        (show σ.u + 1 ≤ σ.n from hu1) hc hq (fun j h1 h2 h3 => UPS.of_eq (by uw_ext)
          (hK j (Nat.le_of_succ_le h1) h2 h3)) (fun hne => h0 ?_)
      rintro ⟨j, h1, h2, h3⟩
      rcases Nat.eq_or_lt_of_le h1 with h | h
      · subst h; exact hD h3
      · exact hne ⟨j, h, h2, h3⟩

/-- **The target search**: from the candidate `u ≤ n`, if some `j ∈ [u, n)` has `bits j` as
the input suffix from the saved position `q`, the machine continues with the least such `j`
as target; if none has, it rejects.

**Proof sketch.** As `ups_ssearch`, with `ups_tcmp`. -/
lemma ups_tsearch (q : ℚ) : ∀ dd (σ : UReg), σ.n - σ.u = dd → σ.Le B → σ.u ≤ σ.n →
    σ.t = 0 → σ.q ≤ x.length → 2 * x.length + 2 ≤ B →
    (∀ j, σ.u ≤ j → j < σ.n → PlainAt x σ.q (Nat.bits j) →
      UPS x B (lc 0) { σ with u := j, t := j, p := x.length, tmp := 0 } q) →
    ((¬ ∃ j, σ.u ≤ j ∧ j < σ.n ∧ PlainAt x σ.q (Nat.bits j)) → q = 0) →
    UPS x B t2 σ q := by
  intro dd
  induction dd with
  | zero =>
    intro σ hd hσ hu _ _ _ _ h0
    refine PSem.jeq_pos rfl (UReg.reg hσ _ _) (by simp; omega) (ups_rej hσ (h0 ?_))
    rintro ⟨j, h1, h2, -⟩; omega
  | succ dd ih =>
    intro σ hd hσ hu ht hq hB hK h0
    have hu1 : σ.u + 1 ≤ σ.n := by omega
    have hd1 : σ.n - (σ.u + 1) = dd := by rw [Nat.sub_add_eq, hd, Nat.add_sub_cancel]
    refine PSem.jeq_neg rfl (UReg.reg hσ _ _) (by simp; omega) ?_
    refine PSem.clr rfl (UReg.reg hσ _ _) ?_
    uw_regs
    refine ups_cp .tTmp q _ (by uw_le) (by simp [cpDst, cpSrc]) ?_
    simp only [cpDst, cpSrc, cpEx]
    uw_regs
    refine PSem.clr rfl (UReg.reg (by uw_le) _ _) ?_
    uw_regs
    refine ups_cp .tP q _ (by uw_le) (by simp [cpDst, cpSrc]) ?_
    simp only [cpDst, cpSrc, cpEx]
    uw_regs
    refine ups_tcmp q _ _ rfl (by uw_le) hB (by dsimp only; omega) (fun hD => ?_)
      (fun hD p' t' hp' ht' => ?_)
    · simp only at hD ⊢
      refine ups_cp .tT q _ (by uw_le) (by simp [cpDst, cpSrc, ht]) ?_
      simp only [cpDst, cpSrc, cpEx]
      uw_regs
      exact UPS.of_eq (by uw_ext) (hK σ.u le_rfl (by omega) hD)
    · simp only at hD ⊢
      refine PSem.inc rfl (UReg.reg (by uw_le) _ _) ?_
      uw_regs
      refine ih { σ with p := p', tmp := t', u := σ.u + 1 }
        hd1 (by uw_le)
        (show σ.u + 1 ≤ σ.n from hu1) ht hq hB (fun j h1 h2 h3 => UPS.of_eq (by uw_ext)
          (hK j (Nat.le_of_succ_le h1) h2 h3)) (fun hne => h0 ?_)
      rintro ⟨j, h1, h2, h3⟩
      rcases Nat.eq_or_lt_of_le h1 with h | h
      · subst h; exact hD h3
      · exact hne ⟨j, h, h2, h3⟩

end Complexity.LogProg
