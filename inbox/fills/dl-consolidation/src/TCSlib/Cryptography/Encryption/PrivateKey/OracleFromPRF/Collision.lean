/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Lazy
import TCSlib.Cryptography.Games.Hopping

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The bad event of the lazy experiment

Step 2 of [PS10, Theorem 168.2]: in the IND experiment with a lazily sampled random function
(`lazyImpl`), the two values of the bit `b` give the same law until the bad flag is raised, and
the flag is raised with probability at most `q(n)² / 2ⁿ` for an adversary making at most `q(n)`
queries.

* *Identical until bad.* Before the challenge the experiment does not read `b`. At the first
  challenge with a new nonce `r*`, the ciphertext `⟨r*, m_b ⊕ y⟩` has a uniform pad `y`; the
  change of variables `y ↦ y ⊕ m₀ ⊕ m₁` (`xorPerm`) maps the ciphertext for `b = 0` to that for
  `b = 1`, and the record `⟨m₀ ‖ m₁, c⟩` is the same. After the challenge, `b` is read only at
  `r*`: by an encryption with nonce `r*`, which raises the flag, or by a decryption, which CPA and
  CCA1 refuse after the challenge (`lazyImpl_agree`).
* *The bad probability.* A query from a good state raises the flag with probability at most
  `(|T| + 1) / 2ⁿ` (`lazyImpl_step`; the first challenge's nonce hits one of the `|T|` points of
  the table, `prob_mem_le`, or an encryption's nonce hits `r*`), and adds at most one point to the
  table (`lazyImpl_grow`). A potential argument sums these over `q` queries (`ProbComp.prob_bad_le`).

## Main results

* `PRFGame.lazyImpl_agree`, `lazyImpl_stick`, `lazyImpl_step`, `lazyImpl_grow`.
* `PRFGame.abs_prob_lazyImpl_sub_le`: the two bits' lazy experiments differ by at most `q² / 2ⁿ`.
* `PRFGame.abs_expect_fImpl_sub_le`: hence so do the experiments with a uniform random function.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 168.2 (book p. 168), the proof's bad event.
* [BR06] M. Bellare, P. Rogaway, *The Security of Triple Encryption and a Framework for
  Code-Based Game-Playing Proofs*, EUROCRYPT 2006 (identical until bad).
-/

namespace TCSlib.Cryptography.Composability.PRFGame

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp ChallengeSim

/-! ### Hitting a list with a uniform sample -/

/-- A key with a value in an association list is one of its keys:
`(T.lookup x).isSome → x ∈ T.map Prod.fst`. -/
theorem mem_keys_of_lookup_isSome {α β : Type} [DecidableEq α] (T : List (α × β)) (x : α)
    (h : (T.lookup x).isSome = true) : x ∈ T.map Prod.fst := by
  induction T with
  | nil => simp at h
  | cons p T ih =>
    obtain ⟨k, v⟩ := p
    rw [List.map_cons]
    by_cases hx : x = k
    · rw [hx]
      exact List.mem_cons_self
    · have hb : (x == k) = false := beq_eq_false_iff_ne.mpr hx
      simp only [List.lookup_cons, hb] at h
      exact List.mem_cons_of_mem _ (ih h)

/-! ### The state readings -/

section Records

variable {n d : ℕ}

/-- Adding a point grows the table by at most one: `|(addPt b st x y hit).1| ≤ |st.1| + 1`. -/
theorem length_addPt_le (b : Bool) (st : LState n d) (x y : Fin n → Bool) (hit : Bool) :
    (addPt b st x y hit).1.length ≤ st.1.length + 1 := by
  rw [addPt_eq]
  split <;> simp

/-- Adding a point raises the flag by `hit`: `(addPt b st x y hit).2.2 = (st.2.2 || hit)`. -/
theorem flag_addPt (b : Bool) (st : LState n d) (x y : Fin n → Bool) (hit : Bool) :
    (addPt b st x y hit).2.2 = (st.2.2 || hit) := by
  rw [addPt_eq]

/-- Away from the challenge's nonce the recorded values do not depend on `b`:
`hitStar st x = false → look b st x = look b' st x`. -/
theorem look_eq_of_hitStar (b b' : Bool) (st : LState n d) (x : Fin n → Bool)
    (h : hitStar st x = false) : look b st x = look b' st x := by
  obtain ⟨T, ch, bd⟩ := st
  cases ch with
  | none => rw [look_none, look_none]
  | some p =>
    obtain ⟨ml, c⟩ := p
    rw [hitStar_some, decide_eq_false_iff_not] at h
    rw [look_some, look_some, if_neg h, if_neg h]

/-- Which points have a recorded value does not depend on `b`:
`(look b st x).isSome = (look b' st x).isSome`. -/
theorem isSome_look_eq (b b' : Bool) (st : LState n d) (x : Fin n → Bool) :
    (look b st x).isSome = (look b' st x).isSome := by
  obtain ⟨T, ch, bd⟩ := st
  cases ch with
  | none => rw [look_none, look_none]
  | some p =>
    obtain ⟨ml, c⟩ := p
    rw [look_some, look_some]
    by_cases h : x = rStar c
    · rw [if_pos h, if_pos h]; rfl
    · rw [if_neg h, if_neg h]

/-- Adding a point does not depend on `b`: `addPt b st x y hit = addPt b' st x y hit`. -/
theorem addPt_eq_of (b b' : Bool) (st : LState n d) (x y : Fin n → Bool) (hit : Bool) :
    addPt b st x y hit = addPt b' st x y hit := by
  rw [addPt_eq, addPt_eq, isSome_look_eq b b']

/-- Exclusive-or with a fixed vector `v`, as a permutation of `{0,1}ⁿ`. -/
def xorPerm (v : Fin n → Bool) : Equiv.Perm (Fin n → Bool) :=
  Function.Involutive.toPerm (fun y i => xor (y i) (v i)) fun y => funext fun i => by
    simp

/-- `xorPerm v y = y ⊕ v`. -/
theorem xorPerm_apply (v y : Fin n → Bool) : xorPerm v y = fun i => xor (y i) (v i) := rfl

/-- **The change of variables at the challenge:** with `|m₀| = |m₁| = n`,
`⟨r, m₀ ⊕ y⟩ = ⟨r, m₁ ⊕ (y ⊕ m₀ ⊕ m₁)⟩`.

**Proof sketch.** Both are `pairEncode ⟦r⟧ _`; compare the second components position by
position: `m₀ᵢ ⊕ yᵢ = m₁ᵢ ⊕ (yᵢ ⊕ m₀ᵢ ⊕ m₁ᵢ)` by cases on the three bits. -/
theorem ctOf_xorPerm (r : Fin n → Bool) {m₀ m₁ : List Bool} (h₀ : m₀.length = n)
    (h₁ : m₁.length = n) (y : Fin n → Bool) :
    ctOf r m₀ y = ctOf r m₁ (xorPerm (padFin n (List.zipWith xor m₀ m₁)) y) := by
  rw [ctOf_eq, ctOf_eq]
  congr 1
  have hv : List.ofFn (padFin n (List.zipWith xor m₀ m₁)) = List.zipWith xor m₀ m₁ :=
    GGMRed.ofFn_padFin_of_length (by simp [h₀, h₁])
  have hY : ∀ v : Fin n → Bool,
      List.ofFn (xorPerm v y) = List.zipWith xor (List.ofFn y) (List.ofFn v) := fun v => by
    apply List.ext_getElem
    · simp
    · intro i _ _
      simp [xorPerm_apply]
  rw [hY, hv]
  apply List.ext_getElem
  · simp [h₀, h₁]
  · intro i hi _
    have hi' : i < n := by simp [h₀] at hi; omega
    have i0 : i < m₀.length := by rw [h₀]; exact hi'
    have i1 : i < m₁.length := by rw [h₁]; exact hi'
    have iy : i < (List.ofFn y).length := by rw [List.length_ofFn]; exact hi'
    simp only [List.getElem_zipWith]
    cases m₀[i] <;> cases m₁[i] <;> cases (List.ofFn y)[i] <;> rfl

/-- The empty state records no value: `ovr b ([], none, false) R = R`. -/
theorem ovr_init (b : Bool) (R : (Fin n → Bool) → (Fin n → Bool)) :
    ovr b (([], none, false) : LState n d) R = R := by
  funext x
  rw [ovr_apply, look_none, List.lookup_nil, Option.getD_none]

end Records

/-! ### The lazy experiment until the bad event -/

section Agree

variable (ins outs : Fin 3 → ℕ) (d n : ℕ) (atk : Attack)

/-- **The two bits agree until bad:** for CPA and CCA1 (decryption refused after the challenge)
and `2n`-bit challenge queries, from a good state the lazy experiments for `b` and `b'` give the
same law to good successors: for every `g`,
`𝔼[ys.2.2.2 ? 0 : g ys] (lazyImpl … b i x s) = 𝔼[ys.2.2.2 ? 0 : g ys] (lazyImpl … b' i x s)`.

**Proof sketch.** An encryption reads `b` only at the challenge's nonce, where it raises the flag
(`look_eq_of_hitStar`, `addPt_eq_of`). A decryption is refused after the challenge and before it
reads the table only. A repeated challenge repeats the record. At the first challenge with a new
nonce, change the pad by `xorPerm (m₀ ⊕ m₁)` (`expect_sample_equiv`, `ctOf_xorPerm`). -/
theorem lazyImpl_agree (hatk : FixedLengthScheme.decOpen atk true = false) (hi2 : ins 2 = n + n)
    (b b' : Bool) (i : Fin 3) (x : (bitSpec ins outs).dom i) (s : LState n d)
    (hs : ¬ s.2.2 = true) (g : (bitSpec ins outs).rng i × LState n d → ℝ) :
    expect (lazyImpl ins outs d n atk b i x s) (fun ys => if ys.2.2.2 = true then 0 else g ys) =
      expect (lazyImpl ins outs d n atk b' i x s)
        (fun ys => if ys.2.2.2 = true then 0 else g ys) := by
  match i, x, g with
  | 0, m, g =>
    simp only [lazyImpl_enc, expect_bind, expect_pure, addPt_eq_of b b' s]
    refine congrArg _ (funext fun r => congrArg _ (funext fun y => ?_))
    cases h : hitStar s r
    · rw [look_eq_of_hitStar b b' s r h]
    · simp [flag_addPt]
  | 1, c, g =>
    obtain ⟨T, ch, bd⟩ := s
    cases ch with
    | some p =>
      have hcl : (FixedLengthScheme.decOpen atk ((T, some p, bd) : LState n d).2.1.isSome &&
          decWF n (List.ofFn c)) = false := by
        show (FixedLengthScheme.decOpen atk true && _) = false
        rw [hatk, Bool.false_and]
      rw [lazyImpl_dec_closed ins outs d n atk b c _ hcl,
        lazyImpl_dec_closed ins outs d n atk b' c _ hcl]
    | none =>
      by_cases hop : (FixedLengthScheme.decOpen atk ((T, none, bd) : LState n d).2.1.isSome &&
          decWF n (List.ofFn c)) = true
      · rw [lazyImpl_dec_open ins outs d n atk b c _ hop,
          lazyImpl_dec_open ins outs d n atk b' c _ hop]
        simp only [look_none, addPt_eq_of b b' ((T, none, bd) : LState n d)]
      · rw [lazyImpl_dec_closed ins outs d n atk b c _ (Bool.eq_false_iff.2 hop),
          lazyImpl_dec_closed ins outs d n atk b' c _ (Bool.eq_false_iff.2 hop)]
  | 2, mm, g =>
    obtain ⟨T, ch, bd⟩ := s
    cases ch with
    | some p =>
      obtain ⟨ml, c⟩ := p
      rw [lazyImpl_challenge_some, lazyImpl_challenge_some]
    | none =>
      have hbd : bd = false := Bool.eq_false_iff.2 hs
      subst hbd
      have hml : (List.ofFn mm).length = n + n := by rw [List.length_ofFn, hi2]
      have hm : ∀ b₀, (AdaptiveCPA.msgOf n b₀ (List.ofFn mm)).length = n := fun b₀ => by
        rw [AdaptiveCPA.msgOf_eq]
        cases b₀ <;> simp [hml]
      simp only [lazyImpl_challenge_none, expect_bind, expect_pure, look_none]
      refine congrArg _ (funext fun r => ?_)
      cases hr : T.lookup r with
      | some y₀ => simp
      | none =>
        simp only [Option.getD_none, Option.isSome_none, Bool.or_false, Bool.false_eq_true,
          if_false]
        refine Eq.trans ?_ (expect_sample_equiv (xorPerm (padFin n (List.zipWith xor
          (AdaptiveCPA.msgOf n b (List.ofFn mm)) (AdaptiveCPA.msgOf n b' (List.ofFn mm))))) _)
        refine congrArg _ (funext fun y => ?_)
        rw [ctOf_xorPerm r (hm b) (hm b') y]

/-- **The flag stays raised:** if `s.2.2 = true`, every outcome `ys` of
`lazyImpl … b i x s` has `ys.2.2.2 = true`.

**Proof sketch.** By the oracle: every branch keeps the flag or ors it with a new bit
(`addPt_eq`, `lazyImpl_*`). -/
theorem lazyImpl_stick (b : Bool) (i : Fin 3) (x : (bitSpec ins outs).dom i) (s : LState n d)
    (hs : s.2.2 = true) :
    (lazyImpl ins outs d n atk b i x s).AllOutputs fun ys => ys.2.2.2 = true := by
  match i, x with
  | 0, m =>
    rw [lazyImpl_enc]
    exact OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun r _ =>
      OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun y _ =>
        OracleComp.allOutputs_pure.2 (by rw [flag_addPt, hs, Bool.true_or])
  | 1, c =>
    by_cases hop : (FixedLengthScheme.decOpen atk s.2.1.isSome && decWF n (List.ofFn c)) = true
    · rw [lazyImpl_dec_open ins outs d n atk b c s hop]
      exact OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun y _ =>
        OracleComp.allOutputs_pure.2 (by rw [flag_addPt, hs, Bool.true_or])
    · rw [lazyImpl_dec_closed ins outs d n atk b c s (Bool.eq_false_iff.2 hop)]
      exact OracleComp.allOutputs_pure.2 hs
  | 2, mm =>
    obtain ⟨T, ch, bd⟩ := s
    cases ch with
    | some p =>
      obtain ⟨ml, c⟩ := p
      rw [lazyImpl_challenge_some]
      exact OracleComp.allOutputs_pure.2 hs
    | none =>
      have hbd : bd = true := hs
      subst hbd
      rw [lazyImpl_challenge_none]
      exact OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun r _ =>
        OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun y _ =>
          OracleComp.allOutputs_pure.2 rfl

/-- **Each query grows the table by at most one point:** every outcome `ys` of
`lazyImpl … b i x s` has `|ys.2.1| ≤ |s.1| + 1`.

**Proof sketch.** By the oracle: encryptions and open decryptions add at most one point
(`length_addPt_le`); challenges, closed decryptions and repeats keep the table. -/
theorem lazyImpl_grow (b : Bool) (i : Fin 3) (x : (bitSpec ins outs).dom i) (s : LState n d) :
    (lazyImpl ins outs d n atk b i x s).AllOutputs fun ys => ys.2.1.length ≤ s.1.length + 1 := by
  match i, x with
  | 0, m =>
    rw [lazyImpl_enc]
    exact OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun r _ =>
      OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun y _ =>
        OracleComp.allOutputs_pure.2 (length_addPt_le b s r y _)
  | 1, c =>
    by_cases hop : (FixedLengthScheme.decOpen atk s.2.1.isSome && decWF n (List.ofFn c)) = true
    · rw [lazyImpl_dec_open ins outs d n atk b c s hop]
      exact OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun y _ =>
        OracleComp.allOutputs_pure.2 (length_addPt_le b s _ y _)
    · rw [lazyImpl_dec_closed ins outs d n atk b c s (Bool.eq_false_iff.2 hop)]
      exact OracleComp.allOutputs_pure.2 (Nat.le_succ _)
  | 2, mm =>
    obtain ⟨T, ch, bd⟩ := s
    cases ch with
    | some p =>
      obtain ⟨ml, c⟩ := p
      rw [lazyImpl_challenge_some]
      exact OracleComp.allOutputs_pure.2 (Nat.le_succ _)
    | none =>
      rw [lazyImpl_challenge_none]
      exact OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun r _ =>
        OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun y _ =>
          OracleComp.allOutputs_pure.2 (Nat.le_succ _)

/-- **Each query raises the flag with probability at most `(|T| + 1) / 2ⁿ`.** An encryption raises
it when its nonce is the challenge's (probability `1 / 2ⁿ`); the first challenge when its nonce is
one of the table's `|T|` points (`prob_mem_le`); decryptions and repeated challenges never.

**Proof sketch.** Write the probability as an expectation over the sampled nonce and bound the
indicator of the flag by the indicator of membership in a list of at most `|T| + 1` points;
conclude with `expect_sample_mem_le`. -/
theorem lazyImpl_step (b : Bool) (i : Fin 3) (x : (bitSpec ins outs).dom i) (s : LState n d)
    (hs : ¬ s.2.2 = true) :
    prob (lazyImpl ins outs d n atk b i x s) (fun ys => ys.2.2.2 = true) ≤
      (s.1.length + 1) * (1 / 2 ^ n) := by
  have hcard : (Fintype.card (Fin n → Bool) : ℝ) = 2 ^ n := by simp
  have hpos : (0 : ℝ) ≤ 1 / 2 ^ n := by positivity
  obtain ⟨T, ch, bd⟩ := s
  have hbd : bd = false := Bool.eq_false_iff.2 hs
  subst hbd
  have hrhs : (0 : ℝ) ≤ ((T, ch, false) : LState n d).1.length + 1 := by positivity
  match i, x with
  | 0, m =>
    rw [prob_eq_expect]
    simp only [lazyImpl_enc, expect_bind, expect_pure, flag_addPt, Bool.false_or, expect_const]
    cases ch with
    | none =>
      simp only [hitStar_none, Bool.false_eq_true, if_false, expect_const]
      exact mul_nonneg hrhs hpos
    | some p =>
      obtain ⟨ml, c⟩ := p
      refine (expect_mono _ fun r => ?_).trans ((expect_sample_mem_le [rStar c]).trans ?_)
      · rw [hitStar_some]
        by_cases h : r = rStar c <;> simp [h]
      · rw [hcard, List.length_singleton, Nat.cast_one, one_div]
        rw [← one_div]
        exact le_mul_of_one_le_left hpos (by simp)
  | 1, c =>
    rw [prob_eq_zero_of_allOutputs]
    · exact mul_nonneg hrhs hpos
    · by_cases hop : (FixedLengthScheme.decOpen atk ch.isSome && decWF n (List.ofFn c)) = true
      · rw [lazyImpl_dec_open ins outs d n atk b c _ hop]
        exact OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun y _ =>
          OracleComp.allOutputs_pure.2 (by rw [flag_addPt]; simp)
      · rw [lazyImpl_dec_closed ins outs d n atk b c _ (Bool.eq_false_iff.2 hop)]
        exact OracleComp.allOutputs_pure.2 (by simp)
  | 2, mm =>
    cases ch with
    | some p =>
      obtain ⟨ml, c⟩ := p
      rw [lazyImpl_challenge_some, prob_eq_zero_of_allOutputs
        (OracleComp.allOutputs_pure.2 (by simp))]
      exact mul_nonneg hrhs hpos
    | none =>
      rw [prob_eq_expect]
      simp only [lazyImpl_challenge_none, expect_bind, expect_pure, look_none, Bool.false_or]
      refine (expect_mono _ fun r => ?_).trans ((expect_sample_mem_le (T.map Prod.fst)).trans ?_)
      · by_cases h : (T.lookup r).isSome = true
        · simp only [h, ↓reduceIte, expect_const, if_pos (mem_keys_of_lookup_isSome T r h),
            le_refl]
        · rw [Bool.not_eq_true] at h
          simp only [h, Bool.false_eq_true, ↓reduceIte, expect_const]
          split_ifs <;> norm_num
      · rw [hcard, List.length_map, div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_right (by simp) hpos

/-- **The two bits' lazy experiments differ by at most `q² / 2ⁿ`** [PS10, Thm 168.2, proof]:
for CPA and CCA1, `2n`-bit challenge queries and a computation making at most `q` queries, the
probabilities of any event on its output differ by at most `q² / 2ⁿ`.

**Proof sketch.** Identical until bad (`identical_until_bad` with `lazyImpl_agree`,
`lazyImpl_stick`), and the potential bound on the flag (`prob_bad_le` with `lazyImpl_step`,
`lazyImpl_grow`) from the empty table. -/
theorem abs_prob_lazyImpl_sub_le (hatk : FixedLengthScheme.decOpen atk true = false)
    (hi2 : ins 2 = n + n) {α : Type} (c : OracleComp (bitSpec ins outs) α) (P : α → Prop)
    (q : ℕ) (hc : c.CostBoundedBy (fun _ => 1) q) :
    |prob (simulate (lazyImpl ins outs d n atk false) c (([], none, false) : LState n d))
          (fun r => P r.1) -
        prob (simulate (lazyImpl ins outs d n atk true) c (([], none, false) : LState n d))
          (fun r => P r.1)| ≤ q ^ 2 / 2 ^ n := by
  have h1 := identical_until_bad (fun st : LState n d => st.2.2 = true)
    (fun i x s hs g => lazyImpl_agree ins outs d n atk hatk hi2 false true i x s hs g)
    (fun i x s hs => lazyImpl_stick ins outs d n atk false i x s hs)
    (fun i x s hs => lazyImpl_stick ins outs d n atk true i x s hs) c P
    (s := (([], none, false) : LState n d)) Bool.false_ne_true
  have h2 := prob_bad_le (impl := lazyImpl ins outs d n atk false)
    (fun st : LState n d => st.2.2 = true) (fun st => st.1.length) (δ := 1 / 2 ^ n)
    (by positivity) (fun i x s hs => lazyImpl_step ins outs d n atk false i x s hs)
    (fun i x s => lazyImpl_grow ins outs d n atk false i x s) c q hc
    (([], none, false) : LState n d) Bool.false_ne_true
  refine h1.trans (h2.trans (le_of_eq ?_))
  simp only [List.length_nil, Nat.cast_zero, zero_add]
  ring

/-- **Step 2 of [PS10, Thm 168.2]: with a random function the bit is hidden up to `q² / 2ⁿ`.**
For CPA and CCA1, `d = 3n + 2`, `2n`-bit challenge queries and computations `C r` (over coins
`r`) making at most `q` queries, the experiments with a uniform random function for `b = 0` and
`b = 1` accept with probabilities at most `q² / 2ⁿ` apart.

**Proof sketch.** For each `b` and coins `r`, averaging over the function is the lazy experiment
from the empty state (`expect_lazyImpl`; the override of the empty state is the function itself);
pointwise in `r` the lazy experiments differ by at most `q² / 2ⁿ` (`abs_prob_lazyImpl_sub_le`);
average over `r` (`abs_expect_sub_le`). -/
theorem abs_expect_fImpl_sub_le (hatk : FixedLengthScheme.decOpen atk true = false)
    (hd : d = 3 * n + 2) (hi2 : ins 2 = n + n) {ρ α : Type} [Fintype ρ] [Nonempty ρ]
    (C : ρ → OracleComp (bitSpec ins outs) α) (P : α → Prop) [DecidablePred P] (q : ℕ)
    (hC : ∀ r, (C r).CostBoundedBy (fun _ => 1) q) :
    |expect (sample ((Fin n → Bool) → (Fin n → Bool))) (fun R => expect (sample ρ) fun r =>
        expect (simulate (fImpl ins outs d n atk false R) (C r) none)
          (fun p => if P p.1 then (1 : ℝ) else 0)) -
      expect (sample ((Fin n → Bool) → (Fin n → Bool))) (fun R => expect (sample ρ) fun r =>
        expect (simulate (fImpl ins outs d n atk true R) (C r) none)
          (fun p => if P p.1 then (1 : ℝ) else 0))| ≤ q ^ 2 / 2 ^ n := by
  have key : ∀ (b : Bool) (r : ρ),
      expect (sample ((Fin n → Bool) → (Fin n → Bool))) (fun R =>
          expect (simulate (fImpl ins outs d n atk b R) (C r) none)
            (fun p => if P p.1 then (1 : ℝ) else 0)) =
        prob (simulate (lazyImpl ins outs d n atk b) (C r) (([], none, false) : LState n d))
          (fun p => P p.1) := fun b r => by
    have h := expect_lazyImpl ins outs d n atk b hd hi2 (fun a => if P a then (1 : ℝ) else 0) (C r)
      (([], none, false) : LState n d)
    simp only [ovr_init, Option.map_none] at h
    rw [h, prob_eq_expect]
  rw [expect_sample_comm, expect_sample_comm (α := (Fin n → Bool) → (Fin n → Bool))]
  simp only [key]
  exact abs_expect_sub_le _ fun r =>
    abs_prob_lazyImpl_sub_le ins outs d n atk hatk hi2 (C r) P q (hC r)

end Agree

end TCSlib.Cryptography.Composability.PRFGame
