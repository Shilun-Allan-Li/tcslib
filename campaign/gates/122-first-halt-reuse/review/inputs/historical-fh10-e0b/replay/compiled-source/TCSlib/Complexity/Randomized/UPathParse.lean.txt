/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.UPathLoops

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The deterministic checks of the random-walk machine: layout and symmetry

[AB09, Theorem 7.19]: the first phases of `Complexity.LogProg.upA` read the unary prefix, the
shape of the matrix field, and the symmetry of the matrix, without coins. In the
probabilistic continuation semantics each phase lemma has two continuation hypotheses: if
the check succeeds, the semantics of the continuation is the target probability `q`; if it
fails, the machine rejects, so `q` must be `0`. The unary and matrix scans follow
`Complexity.LogProg.ps_unary` and `Complexity.LogProg.ps_mat`.

## Main definitions

None: the results are phase lemmas about `Complexity.LogProg.upA`.

## Main results

* `Complexity.LogProg.ups_unary`, `Complexity.LogProg.ups_mat` — the layout checks.
* `Complexity.LogProg.ups_ycol`, `Complexity.LogProg.ups_yrow` — the symmetry test.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.7.)
-/

namespace Complexity.LogProg

open Turing ULabel UPathTac

variable {x : List Bool} {B : ℕ}

/-- A rejection has probability `q` exactly when `q = 0`. -/
lemma ups_rej {σ : UReg} {q : ℚ} (hσ : σ.Le B) (hq : q = 0) : UPS x B rej σ q :=
  (PSem.rej rfl (UReg.reg hσ _ _)).congr hq.symm

/-- **The unary scan**: from pair `k = n` (the count so far), if the unary prefix ends at
pair `n' ≥ k` the machine continues with `n'`; if it ends nowhere, the machine rejects.

**Proof sketch.** Strong induction on `|x| - p`, as `Complexity.LogProg.ps_unary`: `11`
counts one more, `01` ends the prefix, `00` and `10` reject — and then no `n' ≥ k` ends it. -/
lemma ups_unary (q : ℚ) : ∀ dd (σ : UReg), x.length - σ.p = dd → σ.Le B →
    2 * x.length + 2 ≤ B → σ.p = 2 * σ.n → σ.p ≤ x.length →
    (∀ n', σ.n ≤ n' → UnaryRest x σ.n n' → UPS x B m0 { σ with p := 2 * n' + 2, n := n' } q) →
    ((¬ ∃ n', σ.n ≤ n' ∧ UnaryRest x σ.n n') → q = 0) →
    UPS x B u0 σ q := by
  intro dd
  induction dd using Nat.strong_induction_on with
  | _ dd ih =>
  intro σ hd hσ hB hp hpx hK h0
  have hb0' : ∀ b, x.getD σ.p false = b → x.getD (2 * σ.n) false = b := fun b h => hp ▸ h
  have hb1' : ∀ b, x.getD (σ.p + 1) false = b → x.getD (2 * σ.n + 1) false = b :=
    fun b h => hp ▸ h
  cases hb0 : x.getD σ.p false
  · refine PSem.call_neg rfl (UReg.reg hσ _ _) (by simp only [UReg.v_0, pathOr_bit, hb0]) ?_
    refine PSem.inc rfl (UReg.reg hσ _ _) ?_
    uw_regs
    cases hb1 : x.getD (σ.p + 1) false
    · refine PSem.call_neg rfl (UReg.reg (by uw_le) _ _)
        (by simp only [UReg.v_0, pathOr_bit, hb1]) (ups_rej (by uw_le) (h0 ?_))
      rintro ⟨n', hn', hU⟩
      rcases Nat.eq_or_lt_of_le hn' with h | h
      · subst h; have := hU.2.2; rw [hb1' false hb1] at this; exact absurd this (by simp)
      · have := (hU.1 σ.n le_rfl h).1; rw [hb0' false hb0] at this; exact absurd this (by simp)
    · have hlt : σ.p + 1 < x.length := lt_of_getD_true hb1
      refine PSem.call_pos rfl (UReg.reg (by uw_le) _ _)
        (by simp only [UReg.v_0, pathOr_bit, hb1]) ?_
      refine PSem.inc rfl (UReg.reg (by uw_le) _ _) ?_
      uw_regs
      have hU : UnaryRest x σ.n σ.n :=
        ⟨fun i h1 h2 => absurd h2 (by omega), hb0' _ hb0, hb1' _ hb1⟩
      exact UPS.of_eq (by uw_ext) (hK σ.n le_rfl hU)
  · have hlt0 : σ.p < x.length := lt_of_getD_true hb0
    refine PSem.call_pos rfl (UReg.reg hσ _ _) (by simp only [UReg.v_0, pathOr_bit, hb0]) ?_
    refine PSem.inc rfl (UReg.reg hσ _ _) ?_
    uw_regs
    cases hb1 : x.getD (σ.p + 1) false
    · refine PSem.call_neg rfl (UReg.reg (by uw_le) _ _)
        (by simp only [UReg.v_0, pathOr_bit, hb1]) (ups_rej (by uw_le) (h0 ?_))
      rintro ⟨n', hn', hU⟩
      rcases Nat.eq_or_lt_of_le hn' with h | h
      · subst h; have := hU.2.1; rw [hb0' true hb0] at this; exact absurd this (by simp)
      · have := (hU.1 σ.n le_rfl h).2; rw [hb1' false hb1] at this; exact absurd this (by simp)
    · have hlt : σ.p + 1 < x.length := lt_of_getD_true hb1
      refine PSem.call_pos rfl (UReg.reg (by uw_le) _ _)
        (by simp only [UReg.v_0, pathOr_bit, hb1]) ?_
      refine PSem.inc rfl (UReg.reg (by uw_le) _ _) ?_
      uw_regs
      refine PSem.inc rfl (UReg.reg (by uw_le) _ _) ?_
      uw_regs
      let σ₁ : UReg := { σ with p := σ.p + 2, n := σ.n + 1 }
      refine UPS.of_eq (σ' := σ₁) (by ext <;> simp [σ₁]) ?_
      refine ih (x.length - σ₁.p) (by dsimp only [σ₁]; omega) σ₁ rfl
        (by simp only [UReg.Le, σ₁] at hσ ⊢; omega) hB (by dsimp only [σ₁]; omega)
        (by dsimp only [σ₁]; omega) (fun n' h1 h2 => ?_) (fun hne => h0 ?_)
      · refine hK n' (by dsimp only [σ₁] at h1; omega) ⟨fun i hi1 hi2 => ?_, h2.2⟩
        rcases Nat.eq_or_lt_of_le hi1 with h | h
        · subst h; exact ⟨hb0' _ hb0, hb1' _ hb1⟩
        · exact h2.1 i (by dsimp only [σ₁]; omega) hi2
      · rintro ⟨n', h1, h2⟩
        refine hne ⟨n', ?_, fun i hi1 hi2 => h2.1 i (by dsimp only [σ₁] at hi1; omega) hi2,
          h2.2⟩
        dsimp only [σ₁]
        rcases Nat.eq_or_lt_of_le h1 with h | h
        · exfalso; subst h; have := h2.2.1; rw [hb0' _ hb0] at this; simp at this
        · omega

/-- **The matrix scan**: from pair `i ≤ n²` with row `i / n` and column `i % n`, if the
matrix field is well formed from pair `i` on the machine continues past its separator; if
not, it rejects.

**Proof sketch.** Induction on `n² - i`, as `Complexity.LogProg.ps_mat`: a pointer outside
the input rejects; a data pair before pair `n²` advances the column (and the row at the end
of a row); a separator is accepted exactly at pair `n²`. -/
lemma ups_mat (q : ℚ) : ∀ dd i (σ : UReg), σ.n * σ.n - i = dd → σ.Le B →
    2 * x.length + 2 ≤ B → σ.n ≤ x.length →
    σ.p = 2 * σ.n + 2 + 2 * i → σ.a = i / σ.n → σ.b = i % σ.n → i ≤ σ.n * σ.n →
    (MatRest x σ.n i →
      UPS x B (cp .yq) { σ with p := 2 * σ.n + 2 + 2 * (σ.n * σ.n) + 2, a := σ.n, b := 0 } q) →
    (¬ MatRest x σ.n i → q = 0) →
    UPS x B m0 σ q := by
  intro dd
  induction dd using Nat.strong_induction_on with
  | _ dd ih =>
  intro i σ hd hσ hB hn hp ha hb hi hK h0
  have hlastiff : σ.a = σ.n ↔ i = σ.n * σ.n := by rw [ha]; exact div_eq_self_iff hi
  -- a data pair (equal bits) at `p, p + 1`, the pointer on its second bit
  have hdata : σ.p < x.length → x.getD σ.p false = x.getD (σ.p + 1) false →
      UPS x B m5 { σ with p := σ.p + 1 } q := by
    intro hpx heq
    by_cases hlast : i = σ.n * σ.n
    · refine PSem.jeq_pos rfl (UReg.reg (by uw_le) _ _) (by simpa using hlastiff.mpr hlast)
        (ups_rej (by uw_le) (h0 fun hM => ?_))
      have h1 := hM.2.1; have h2 := hM.2.2
      rw [← hlast, ← hp] at h1 h2
      rw [← heq, h1] at h2; exact absurd h2 (by simp)
    · have hlt : i < σ.n * σ.n := by omega
      have hpos : 0 < σ.n := Nat.pos_of_ne_zero fun h => by rw [h] at hlt; simp at hlt
      refine PSem.jeq_neg rfl (UReg.reg (by uw_le) _ _)
        (by simp only [UReg.v_1, UReg.v_2]; exact fun h => hlast (hlastiff.mp h)) ?_
      refine PSem.inc rfl (UReg.reg (by uw_le) _ _) ?_
      uw_regs
      refine PSem.inc rfl (UReg.reg (by uw_le) _ _) ?_
      uw_regs
      have hrec : ∀ a' b', a' = (i + 1) / σ.n → b' = (i + 1) % σ.n →
          UPS x B m0 { σ with p := σ.p + 2, a := a', b := b' } q := by
        intro a' b' e3 e4
        have ha2 : a' ≤ σ.n := by rw [e3]; exact Nat.div_le_of_le_mul (by omega)
        have hb2 : b' < σ.n := by rw [e4]; exact Nat.mod_lt _ hpos
        refine ih (σ.n * σ.n - (i + 1)) (by omega) (i + 1)
          { σ with p := σ.p + 2, a := a', b := b' } rfl (by uw_le) hB hn (by dsimp only; omega)
          e3 e4 (by dsimp only; omega) (fun hM => hK ⟨fun j hj1 hj2 => ?_, hM.2⟩)
          (fun hM => h0 fun hM' => hM ⟨fun j hj1 hj2 => hM'.1 j (by omega) hj2, hM'.2⟩)
        rcases Nat.eq_or_lt_of_le hj1 with h | h
        · subst h; rw [show 2 * σ.n + 2 + 2 * i = σ.p by omega]; exact heq
        · exact hM.1 j (by omega) hj2
      have hds := divmod_succ (i := i) hpos
      have hmod := Nat.mod_lt i hpos
      by_cases hc : i % σ.n + 1 = σ.n
      · refine PSem.jeq_pos rfl (UReg.reg (by uw_le) _ _) (by simp; omega) ?_
        refine PSem.clr rfl (UReg.reg (by uw_le) _ _) ?_
        uw_regs
        have hdiv : i / σ.n < σ.n := Nat.div_lt_of_lt_mul hlt
        refine PSem.inc rfl (UReg.reg (by uw_le) _ _) ?_
        uw_regs
        exact UPS.of_eq (by uw_ext) (hrec (i / σ.n + 1) 0 (hds.1 hc).1.symm (hds.1 hc).2.symm)
      · refine PSem.jeq_neg rfl (UReg.reg (by uw_le) _ _) (by simp; omega) ?_
        exact UPS.of_eq (by uw_ext) (hrec (i / σ.n) (i % σ.n + 1) (hds.2 hc).1.symm
          (hds.2 hc).2.symm)
  by_cases hpx : σ.p < x.length
  · refine PSem.call_pos rfl (UReg.reg hσ _ _)
      (by simp only [UReg.v_0, pathOr_len, decide_eq_true_eq]; exact hpx) ?_
    cases hb0 : x.getD σ.p false
    · refine PSem.call_neg rfl (UReg.reg hσ _ _) (by simp only [UReg.v_0, pathOr_bit, hb0]) ?_
      refine PSem.inc rfl (UReg.reg (by uw_le) _ _) ?_
      uw_regs
      cases hb1 : x.getD (σ.p + 1) false
      · refine PSem.call_neg rfl (UReg.reg (by uw_le) _ _)
          (by simp only [UReg.v_0, pathOr_bit, hb1]) ?_
        exact hdata hpx (by rw [hb0, hb1])
      · refine PSem.call_pos rfl (UReg.reg (by uw_le) _ _)
          (by simp only [UReg.v_0, pathOr_bit, hb1]) ?_
        by_cases hlast : i = σ.n * σ.n
        · refine PSem.jeq_pos rfl (UReg.reg (by uw_le) _ _)
            (by simpa using hlastiff.mpr hlast) ?_
          refine PSem.inc rfl (UReg.reg (by uw_le) _ _) ?_
          uw_regs
          have hx1 : x.getD (2 * σ.n + 2 + 2 * (σ.n * σ.n) + 1) false = true := by
            rw [← hlast, ← hp]; exact hb1
          have hb00 : σ.b = 0 := by rw [hb, hlast, Nat.mul_mod_left]
          have haa : σ.a = σ.n := hlastiff.mpr hlast
          exact UPS.of_eq (by uw_ext) (hK ⟨fun j hj1 hj2 => absurd hj2 (by omega),
            by rw [← hlast, ← hp]; exact hb0, hx1⟩)
        · refine PSem.jeq_neg rfl (UReg.reg (by uw_le) _ _)
            (by simp; exact fun h => hlast (hlastiff.mp h)) (ups_rej (by uw_le) (h0 ?_))
          intro hM
          have := hM.1 i le_rfl (by omega)
          rw [← hp, hb0, hb1] at this; exact absurd this (by simp)
    · refine PSem.call_pos rfl (UReg.reg hσ _ _) (by simp only [UReg.v_0, pathOr_bit, hb0]) ?_
      refine PSem.inc rfl (UReg.reg (by uw_le) _ _) ?_
      uw_regs
      cases hb1 : x.getD (σ.p + 1) false
      · refine PSem.call_neg rfl (UReg.reg (by uw_le) _ _)
          (by simp only [UReg.v_0, pathOr_bit, hb1]) (ups_rej (by uw_le) (h0 ?_))
        intro hM
        by_cases hlast : i = σ.n * σ.n
        · have := hM.2.1; rw [← hlast, ← hp, hb0] at this; exact absurd this (by simp)
        · have := hM.1 i le_rfl (by omega)
          rw [← hp, hb0, hb1] at this; exact absurd this (by simp)
      · refine PSem.call_pos rfl (UReg.reg (by uw_le) _ _)
          (by simp only [UReg.v_0, pathOr_bit, hb1]) ?_
        exact hdata hpx (by rw [hb0, hb1])
  · refine PSem.call_neg rfl (UReg.reg hσ _ _)
      (by simp only [UReg.v_0, pathOr_len, decide_eq_false_iff_not]; exact hpx)
      (ups_rej (by uw_le) (h0 fun hM => ?_))
    have := lt_of_getD_true hM.2.2
    omega

/-- **The symmetry test of one row**: from column `w ≤ n` of row `u < n`, if the matrix
bits of `(u, w')` and `(w', u)` agree for all `w' ∈ [w, n)` the machine continues with the
next row; otherwise it rejects.

**Proof sketch.** Induction on `n - w`: compute the position of `(u, w)` (`ups_index`), read
its bit, compute the position of `(w, u)` (by one of two index sites, according to the first
bit), read it, reject if they differ, and move to the next column. -/
lemma ups_ycol (q : ℚ) :
    ∀ dd (σ : UReg), σ.n - σ.w = dd → σ.Le B → 2 * σ.n + 2 + 2 * (σ.n * σ.n) ≤ B →
    σ.u < σ.n → σ.w ≤ σ.n →
    ((∀ w', σ.w ≤ w' → w' < σ.n → (pathEdge x σ.n σ.u w' ↔ pathEdge x σ.n w' σ.u)) →
      ∀ p a b, p ≤ B → a ≤ B → b ≤ B → UPS x B yn { σ with w := σ.n, p := p, a := a, b := b } q) →
    ((¬ ∀ w', σ.w ≤ w' → w' < σ.n → (pathEdge x σ.n σ.u w' ↔ pathEdge x σ.n w' σ.u)) →
      q = 0) →
    UPS x B y2 σ q := by
  intro dd
  induction dd with
  | zero =>
    intro σ hd hσ _ hu hw hK _
    have he : σ.w = σ.n := by omega
    refine PSem.jeq_pos rfl (UReg.reg hσ _ _) (by simpa using he) ?_
    refine UPS.of_eq ?_ (hK (fun w' h1 h2 => absurd h2 (by omega)) σ.p σ.a σ.b
      hσ.1 hσ.2.2.1 hσ.2.2.2.1)
    ext <;> simp [he]
  | succ dd ih =>
    intro σ hd hσ hmn hu hw hK h0
    have hwn : σ.w < σ.n := by omega
    have hidx₁ := rowMajor_lt hu hwn
    have hidx₂ := rowMajor_lt hwn hu
    refine PSem.jeq_neg rfl (UReg.reg hσ _ _) (by simp; omega) ?_
    refine ups_index .y0 q σ hσ (by simpa [ixRow] using hu) (by simpa [ixCol] using hwn) hmn ?_
    simp only [ixRow, ixCol, ixEx, UReg.v_11, UReg.v_12]
    -- the rest of the row, after a matching pair of bits
    have hnext : (pathEdge x σ.n σ.u σ.w ↔ pathEdge x σ.n σ.w σ.u) → ∀ p a b, p ≤ B → a ≤ B →
        b ≤ B → UPS x B y7 { σ with p := p, a := a, b := b } q := by
      intro hsame p a b hp ha hb
      refine PSem.inc rfl (UReg.reg (by uw_le) _ _) ?_
      uw_regs
      refine ih { σ with p := p, a := a, b := b, w := σ.w + 1 } (by dsimp only; omega)
        (by uw_le) hmn hu (by dsimp only; omega) (fun hS p' a' b' hp' ha' hb' => ?_)
        (fun hS => h0 ?_)
      · refine UPS.of_eq ?_ (hK (fun w' h1 h2 => ?_) p' a' b' hp' ha' hb')
        · ext <;> simp
        · rcases Nat.eq_or_lt_of_le h1 with h | h
          · subst h; exact hsame
          · exact hS w' (by dsimp only; omega) h2
      · exact fun hA => hS fun w' h1 h2 => hA w' (by dsimp only at h1; omega) h2
    have hbad : ¬ (pathEdge x σ.n σ.u σ.w ↔ pathEdge x σ.n σ.w σ.u) → q = 0 :=
      fun hne => h0 fun hA => hne (hA σ.w le_rfl hwn)
    by_cases he₁ : pathEdge x σ.n σ.u σ.w
    · refine PSem.call_pos rfl (UReg.reg (by uw_le) _ _)
        (by simp only [UReg.v_0, pathOr_bit]; exact he₁) ?_
      refine ups_index .y1 q _ (by uw_le) (by simpa [ixRow] using hwn) (by simpa [ixCol] using hu)
        (by simpa using hmn) ?_
      simp only [ixRow, ixCol, ixEx, UReg.v_11, UReg.v_12]
      by_cases he₂ : pathEdge x σ.n σ.w σ.u
      · refine PSem.call_pos rfl (UReg.reg (by uw_le) _ _)
          (by simp only [UReg.v_0, pathOr_bit]; exact he₂) ?_
        exact hnext (iff_of_true he₁ he₂) _ _ _ (by omega) (by uw_le) (by uw_le)
      · refine PSem.call_neg rfl (UReg.reg (by uw_le) _ _)
          (by simp only [UReg.v_0, pathOr_bit]; simpa [pathEdge] using he₂)
          (ups_rej (by uw_le) (hbad fun h => he₂ (h.mp he₁)))
    · refine PSem.call_neg rfl (UReg.reg (by uw_le) _ _)
        (by simp only [UReg.v_0, pathOr_bit]; simpa [pathEdge] using he₁) ?_
      refine ups_index .y2 q _ (by uw_le) (by simpa [ixRow] using hwn) (by simpa [ixCol] using hu)
        (by simpa using hmn) ?_
      simp only [ixRow, ixCol, ixEx, UReg.v_11, UReg.v_12]
      by_cases he₂ : pathEdge x σ.n σ.w σ.u
      · refine PSem.call_pos rfl (UReg.reg (by uw_le) _ _)
          (by simp only [UReg.v_0, pathOr_bit]; exact he₂)
          (ups_rej (by uw_le) (hbad fun h => he₁ (h.mpr he₂)))
      · refine PSem.call_neg rfl (UReg.reg (by uw_le) _ _)
          (by simp only [UReg.v_0, pathOr_bit]; simpa [pathEdge] using he₂) ?_
        exact hnext (iff_of_false he₁ he₂) _ _ _ (by omega) (by uw_le) (by uw_le)

/-- **The symmetry test**: from row `u ≤ n`, if the matrix bits of `(u', w')` and `(w', u')`
agree for all rows `u' ∈ [u, n)` and columns `w' < n` the machine continues with the source
search; otherwise it rejects.

**Proof sketch.** Induction on `n - u`, each row by `ups_ycol`. -/
lemma ups_yrow (q : ℚ) :
    ∀ dd (σ : UReg), σ.n - σ.u = dd → σ.Le B → 2 * σ.n + 2 + 2 * (σ.n * σ.n) ≤ B →
    σ.u ≤ σ.n →
    ((∀ u', σ.u ≤ u' → u' < σ.n → ∀ w', w' < σ.n →
        (pathEdge x σ.n u' w' ↔ pathEdge x σ.n w' u')) →
      ∀ p a b w, p ≤ B → a ≤ B → b ≤ B → w ≤ B →
        UPS x B s0 { σ with u := σ.n, w := w, p := p, a := a, b := b } q) →
    ((¬ ∀ u', σ.u ≤ u' → u' < σ.n → ∀ w', w' < σ.n →
        (pathEdge x σ.n u' w' ↔ pathEdge x σ.n w' u')) → q = 0) →
    UPS x B y0 σ q := by
  intro dd
  induction dd with
  | zero =>
    intro σ hd hσ _ hu hK _
    have he : σ.u = σ.n := by omega
    refine PSem.jeq_pos rfl (UReg.reg hσ _ _) (by simpa using he) ?_
    refine UPS.of_eq ?_ (hK (fun u' h1 h2 => absurd h2 (by omega)) σ.p σ.a σ.b σ.w
      hσ.1 hσ.2.2.1 hσ.2.2.2.1 (by uw_le))
    ext <;> simp [he]
  | succ dd ih =>
    intro σ hd hσ hm hu hK h0
    refine PSem.jeq_neg rfl (UReg.reg hσ _ _) (by simp; omega) ?_
    refine PSem.clr rfl (UReg.reg hσ _ _) ?_
    uw_regs
    refine ups_ycol q _ { σ with w := 0 } rfl (by uw_le) hm (by dsimp only; omega)
      (Nat.zero_le _) (fun hS p a b hp ha hb => ?_) (fun hS => h0 fun hA => hS fun w' _ h2 =>
        hA σ.u le_rfl (by dsimp only at h2 ⊢; omega) w' h2)
    refine PSem.inc rfl (UReg.reg (by uw_le) _ _) ?_
    uw_regs
    refine ih { σ with u := σ.u + 1, w := σ.n, p := p, a := a, b := b } (by dsimp only; omega)
      (by uw_le) hm (by dsimp only; omega) (fun hR p' a' b' w' hp' ha' hb' hw' => ?_)
      (fun hR => h0 ?_)
    · refine UPS.of_eq ?_ (hK (fun u' h1 h2 w'' h3 => ?_) p' a' b' w' hp' ha' hb' hw')
      · ext <;> simp
      · rcases Nat.eq_or_lt_of_le h1 with h | h
        · subst h; exact hS w'' (Nat.zero_le _) h3
        · exact hR u' (by dsimp only; omega) h2 w'' h3
    · exact fun hA => hR fun u' h1 h2 w'' h3 => hA u' (by dsimp only at h1; omega) h2 w'' h3

end Complexity.LogProg
