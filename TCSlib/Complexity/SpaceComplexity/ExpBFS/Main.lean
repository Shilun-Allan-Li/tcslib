/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.ExpBFS.Search
import TCSlib.Complexity.SpaceComplexity.ExpBFS.Radius
import TCSlib.Complexity.SpaceComplexity.Codec.Deciders
import TCSlib.Complexity.SpaceComplexity.Codec.StepDecider

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Nondeterministic space in exponential time, by breadth-first search

The search machine `Complexity.LogProg.ExpBFS.A`, run with the deciders of the code languages
of a nondeterministic decider `N` (`TCSlib.Complexity.SpaceComplexity.Codec`), decides `N`'s
language: at each radius `s = 0, 1, …` it counts the reachable codes at radii `s` and `s + 1`
by breadth-first search, and at the first radius where the counts agree it answers whether a
reachable code at radius `s` is accepting (`Complexity.ExpBFS.mem_iff_of_card_eq`); this
happens by the space bound (`Complexity.ExpBFS.card_rset_succ_of_le`). Its registers hold
numbers below `2 ^ O(S)` and its memory head stays below `2 ^ O(S)`, so by
`Complexity.LogProg.marm_dtime` the language is decided in time `2 ^ O(S)`
[AB09, §4.1.1, Theorem 4.2, third inclusion]. The space bound need not be computed: only
`logSpace ≤ S` is used.

## Main definitions

* `Complexity.LogProg.ExpBFS.decs`, `Complexity.LogProg.ExpBFS.orcN` — the four deciders.

## Main results

* `Complexity.LogProg.ExpBFS.fscan_run` — the final scan.
* `Complexity.LogProg.ExpBFS.iter_run` — the iteration over the radii answers membership.
* `Complexity.NSPACE_subset_exp_dtime_of_le` — `NSPACE S ⊆ ⋃ c, DTIME (2 ^ (c (S n + 1)))`
  whenever `logSpace ≤ S`. [AB09, Theorem 4.2, third inclusion]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1, Theorem 4.2.)
-/

namespace Complexity.LogProg

namespace ExpBFS

open Turing

/-! ## The deciders -/

/-- The deciders of the search machine for `N`: `0` the input length, `1` the initial codes,
`2` the step pairs, `3` the accepting codes. -/
def decs (N : FinNDTM Bool) : Fin 4 → Language Bool :=
  ![inputLenLang, Codec.initLang N, Codec.stepLang N, Codec.acceptLang N]

/-- The answers of the deciders of the search machine for `N`. -/
noncomputable def orcN (N : FinNDTM Bool) : Fin 4 → List Bool → Bool :=
  fun j V => MultiTapeTM.indicator (decs N j : Set (List Bool)) V

variable {N : FinNDTM Bool} {x : List Bool}

/-- Decider `0` answers the input length queries. -/
lemma orcN_len (N : FinNDTM Bool) (x : List Bool) :
    ∀ k ≤ x.length, orcN N 0 (pairEncode x (Nat.bits k)) = decide (k < x.length) := by
  intro k _
  simp only [orcN, decs, Matrix.cons_val_zero, inputLenLang, indicator_indexLang_pairEncode]
  exact decide_eq_decide.mpr Iff.rfl

/-- Decider `1` answers whether a code is the initial code. -/
lemma ini_orcN (r u : ℕ) :
    ini (orcN N) x r u = true ↔ Codec.cfgCode r (N.tm.initCfg x) = u := by
  rw [← Codec.mem_initLang]
  simp [ini, orcN, decs, indicator_eq_decide]

/-- Decider `2` answers the step relation. -/
lemma stp_orcN (r u v : ℕ) : stp (orcN N) x r u v = true ↔ Codec.StepRel N x r u v := by
  simp [stp, orcN, decs, indicator_eq_decide, Codec.StepRel]

/-- Decider `3` answers whether a code is accepting. -/
lemma acc_orcN (r u : ℕ) :
    orcN N 3 (pairEncode x (pairEncode (Nat.bits u) (Nat.bits r))) = true ↔
      pairEncode x (pairEncode (Nat.bits u) (Nat.bits r)) ∈ Codec.acceptLang N := by
  simp [orcN, decs, indicator_eq_decide]

/-- **The codes reachable below `K` are the reachable codes**, once `K` bounds the codes. -/
lemma cl_iff {r K : ℕ} (hK : 2 ^ (Codec.codeK N * (r + logSpace x.length + 1)) ≤ K) (v : ℕ) :
    Cl (orcN N) x r K v ↔ ExpBFS.RCode N x r v := by
  constructor
  · rintro ⟨u, -, hi, hpath⟩
    rw [ini_orcN] at hi
    subst hi
    exact hpath.mono fun a b h => (stp_orcN r a b).mp h.1
  · intro h
    refine ⟨_, (Codec.cfgCode_lt r _).trans_le hK, (ini_orcN r _).mpr rfl, ?_⟩
    have key : ∀ w, ExpBFS.RCode N x r w → Relation.ReflTransGen
        (fun a b => stp (orcN N) x r a b = true ∧ b < K)
        (Codec.cfgCode r (N.tm.initCfg x)) w := by
      intro w hw
      induction hw with
      | refl => exact Relation.ReflTransGen.refl
      | @tail b c hab hbc ih =>
        exact ih.tail ⟨(stp_orcN r b c).mpr hbc,
          (ExpBFS.rcode_lt (hab.tail hbc)).trans_le hK⟩
    exact key v h

open Classical in
/-- The count of a search is the number of reachable codes. -/
lemma card_cl {r K : ℕ} (hK : 2 ^ (Codec.codeK N * (r + logSpace x.length + 1)) ≤ K) :
    ((Finset.range K).filter (Cl (orcN N) x r K)).card = (ExpBFS.rset N x r).card := by
  classical
  rw [← ExpBFS.card_filter_rcode hK]
  exact congrArg Finset.card (Finset.filter_congr fun v _ => cl_iff hK v)

/-! ## The final scan -/

variable {K₀ : ℕ} {orc : Fin 4 → List Bool → Bool} {B P : ℕ}

open Classical in
/-- **The final scan**: from `fU` with `U = u₀`, the machine answers whether some marked code
`u₀ ≤ v < K` is accepting (decider `3` at radius `s`).

**Proof sketch.** Induction on `K - U`: read the mark of `U` (`ac_run`); if marked, ask the
accepting-code decider and accept on a yes; increment `U`; reject at `U = K`. -/
theorem fscan_run : ∀ (j : ℕ) (S : St) (M : ℤ → Bool), S.K - S.U = j → S.U ≤ S.K →
    S.T = 0 → S.T2 = 0 → S.Z = 0 → SBd B P S →
    MHalt (A K₀) orc x (G x B P) (cf .fU S M 0)
      (decide (∃ v, S.U ≤ v ∧ v < S.K ∧ M (cell S.Bs v) = true ∧
        orc 3 (pairEncode x (pairEncode (Nat.bits v) (Nat.bits S.s))) = true)) := by
  classical
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro S M hj hUK hT hT2 hZ hS
  obtain ⟨hbd, hB1, hP1, hK1⟩ := hS
  by_cases hU : S.U = S.K
  · have hno : ¬ ∃ v, S.U ≤ v ∧ v < S.K ∧ M (cell S.Bs v) = true ∧
        orc 3 (pairEncode x (pairEncode (Nat.bits v) (Nat.bits S.s))) = true := by
      rintro ⟨v, h1, h2, -⟩; omega
    rw [decide_eq_false hno]
    refine stepH_of rfl hbd ⟨le_rfl, by omega⟩ ?_
    simp only [astep]; regs [hU, ↓reduceIte]
    exact MHalt.ret rfl (g_of hbd ⟨le_rfl, by omega⟩ _)
  · have hlt : S.U < S.K := by omega
    have hsplit : (∃ v, S.U ≤ v ∧ v < S.K ∧ M (cell S.Bs v) = true ∧
        orc 3 (pairEncode x (pairEncode (Nat.bits v) (Nat.bits S.s))) = true) ↔
        (M (cell S.Bs S.U) = true ∧
          orc 3 (pairEncode x (pairEncode (Nat.bits S.U) (Nat.bits S.s))) = true) ∨
        ∃ v, S.U + 1 ≤ v ∧ v < S.K ∧ M (cell S.Bs v) = true ∧
          orc 3 (pairEncode x (pairEncode (Nat.bits v) (Nat.bits S.s))) = true := by
      constructor
      · rintro ⟨v, h1, h2, h3, h4⟩
        rcases Nat.eq_or_lt_of_le h1 with e | e
        · subst e; exact Or.inl ⟨h3, h4⟩
        · exact Or.inr ⟨v, e, h2, h3, h4⟩
      · rintro (⟨h3, h4⟩ | ⟨v, h1, h2, h3, h4⟩)
        · exact ⟨S.U, le_rfl, hlt, h3, h4⟩
        · exact ⟨v, by omega, h2, h3, h4⟩
    have hbd1 : St.Bd B { S with U := S.U + 1 } := by simp only [St.Bd] at hbd ⊢; omega
    have rest := ih (S.K - (S.U + 1)) (by omega) { S with U := S.U + 1 } M rfl
      (by simp only; omega) hT hT2 hZ ⟨hbd1, hB1, hP1, hK1⟩
    simp only at rest
    -- the next code
    have next : MHalt (A K₀) orc x (G x B P) (cf .fN S M 0)
        (decide (∃ v, S.U + 1 ≤ v ∧ v < S.K ∧ M (cell S.Bs v) = true ∧
          orc 3 (pairEncode x (pairEncode (Nat.bits v) (Nat.bits S.s))) = true)) := by
      refine stepH_of rfl hbd ⟨le_rfl, by omega⟩ ?_
      simp only [astep]; regs
      exact rest
    refine stepH_of rfl hbd ⟨le_rfl, by omega⟩ ?_
    simp only [astep]; regs; rw [if_neg hU]
    have hac := ac_run (orc := orc) (x := x) (B := B) (P := P) (K₀ := K₀) .fU S M hbd hT
      hT2 hZ (by simp [Site.idx]; omega) (by simp [Site.idx]; omega)
    simp only [Site.set, Site.idx, St.toV_U, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
      acExit] at hac
    refine hac.halt ?_
    -- skipping the code `U`
    have hskip : ¬ (M (cell S.Bs S.U) = true ∧
        orc 3 (pairEncode x (pairEncode (Nat.bits S.U) (Nat.bits S.s))) = true) →
        decide (∃ v, S.U ≤ v ∧ v < S.K ∧ M (cell S.Bs v) = true ∧
          orc 3 (pairEncode x (pairEncode (Nat.bits v) (Nat.bits S.s))) = true) =
        decide (∃ v, S.U + 1 ≤ v ∧ v < S.K ∧ M (cell S.Bs v) = true ∧
          orc 3 (pairEncode x (pairEncode (Nat.bits v) (Nat.bits S.s))) = true) := by
      intro hno
      exact decide_eq_decide.mpr (hsplit.trans (or_iff_right hno))
    by_cases hb : M (cell S.Bs S.U) = true
    · simp only [hb, ↓reduceIte]
      refine stepH_of rfl hbd ⟨le_rfl, by omega⟩ ?_
      simp only [astep, vword_whole₂]; regs
      by_cases ha : orc 3 (pairEncode x (pairEncode (Nat.bits S.U) (Nat.bits S.s))) = true
      · simp only [ha, ↓reduceIte]
        rw [decide_eq_true ⟨S.U, le_rfl, hlt, hb, ha⟩]
        exact MHalt.ret rfl (g_of hbd ⟨le_rfl, by omega⟩ _)
      · rw [hskip (fun h => ha h.2)]
        rw [Bool.not_eq_true] at ha
        simp only [ha, Bool.false_eq_true, ↓reduceIte]
        exact next
    · rw [hskip (fun h => hb h.1)]
      rw [Bool.not_eq_true] at hb
      simp only [hb, Bool.false_eq_true, ↓reduceIte]
      exact next

/-! ## The iteration over the radii -/

/-- The code bound at radius `s` on inputs of length `n`. -/
def kb (N : FinNDTM Bool) (n s : ℕ) : ℕ := 2 ^ (Codec.codeK N * (s + lgv n + 1))

/-- The code width factor is at least `2`. -/
lemma two_le_codeK (N : FinNDTM Bool) : 2 ≤ Codec.codeK N := by
  simp only [Codec.codeK]; omega

/-- The code bound at the next radius is at least four times larger. -/
lemma four_mul_kb_le (N : FinNDTM Bool) (n s : ℕ) : 4 * kb N n s ≤ kb N n (s + 1) := by
  have h2 := two_le_codeK N
  have e : Codec.codeK N * (s + 1 + lgv n + 1) =
      Codec.codeK N * (s + lgv n + 1) + Codec.codeK N := by ring
  simp only [kb, e, pow_add]
  rw [mul_comm]
  exact Nat.mul_le_mul_left _ (by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ Codec.codeK N := Nat.pow_le_pow_right (by norm_num) h2)

/-- The code bound grows with the radius. -/
lemma kb_mono (N : FinNDTM Bool) (n : ℕ) {s s' : ℕ} (h : s ≤ s') : kb N n s ≤ kb N n s' :=
  Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (by omega))

/-- The code bound bounds the codes. -/
lemma code_bound_le (N : FinNDTM Bool) (n s : ℕ) :
    2 ^ (Codec.codeK N * (s + logSpace n + 1)) ≤ kb N n s :=
  Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (by have := logSpace_le_lgv n; omega))

/-- The register bound of the machine on inputs of length `n` with space bound `t`. -/
def bigB (N : FinNDTM Bool) (n t : ℕ) : ℕ := 3 * kb N n (t + 1) + n + 3

/-- A count of codes below `K` is at most `K`. -/
lemma card_filter_range_le (K : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    ((Finset.range K).filter p).card ≤ K :=
  (Finset.card_filter_le _ _).trans (by simp)

/-- The radius and the width are below the code bound. -/
lemma lt_kb (N : FinNDTM Bool) (n s : ℕ) :
    Codec.codeK N * (s + lgv n + 1) < kb N n s := Nat.lt_two_pow_self

/-- The register file at the start of an iteration at radius `s`. -/
def st1 (n s c1 : ℕ) : St := { St.zero with Lg := lgv n, s := s, c1 := c1 }

/-- The register file after copying the radius into `s1`. -/
def st2 (n s c1 : ℕ) : St := { St.zero with Lg := lgv n, s := s, c1 := c1, s1 := s }

/-- The register file at the start of the second search. -/
def st3 (n s c1 : ℕ) : St := { St.zero with Lg := lgv n, s := s, c1 := c1, s1 := s + 1 }

/-- The register file at the start of the final scan. -/
def st5 (n s c1 : ℕ) : St :=
  { St.zero with Lg := lgv n, s := s, c1 := c1, s1 := s + 1, c := c1 }

open Classical in
/-- **The iteration over the radii.** On input `x`, for a decider `N` of `L` in space `sp`,
from the first width computation at radius `s ≤ sp |x|`, with the memory marked only below
`2 K_s`, the machine answers `x ∈ L`.

**Proof sketch.** Strong induction on `sp |x| - s`. Two searches (`wk_run`, `search_run`)
count the reachable codes at radii `s` and `s + 1` (`card_cl`) in fresh regions
`[2K_s, 3K_s)` and `[K_{s+1}, 2K_{s+1})` (`four_mul_kb_le`). If the counts agree, the final
scan (`fscan_run`) over the first search's marks answers membership
(`Complexity.ExpBFS.mem_iff_of_card_eq`); otherwise `s < sp |x|`
(`Complexity.ExpBFS.card_rset_succ_of_le`) and the iteration continues at `s + 1`. -/
theorem iter_run {L : Language Bool} {sp : ℕ → ℕ} (hN : N.DecidesInSpace L sp) :
    ∀ (d s : ℕ) (M : ℤ → Bool), sp x.length - s = d → s ≤ sp x.length →
      (∀ z, M z = true → z < ((2 * kb N x.length s : ℕ) : ℤ)) →
      MHalt (A (Codec.codeK N)) (orcN N) x
        (G x (bigB N x.length (sp x.length)) (3 * kb N x.length (sp x.length + 1)))
        (cf (.cp (.radX .fst) 0) { St.zero with Lg := lgv x.length, s := s } M 0)
        (MultiTapeTM.indicator (L : Set (List Bool)) x) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro s M hd hs hM
  have hK02 : 2 ≤ Codec.codeK N := two_le_codeK N
  have hK0 : 0 < Codec.codeK N := by omega
  have h4 : 4 * kb N x.length s ≤ kb N x.length (s + 1) := four_mul_kb_le N x.length s
  have hmax : kb N x.length (s + 1) ≤ kb N x.length (sp x.length + 1) :=
    kb_mono N x.length (by omega)
  have hlg : lgv x.length ≤ x.length + 1 := lgv_le_succ x.length
  have hwK : Codec.codeK N * (s + lgv x.length + 1) < kb N x.length s := lt_kb N x.length s
  have hw1K : Codec.codeK N * (s + 1 + lgv x.length + 1) < kb N x.length (s + 1) :=
    lt_kb N x.length (s + 1)
  have hsw : s + 1 ≤ Codec.codeK N * (s + 1 + lgv x.length + 1) := by nlinarith
  have hk0 : kb N x.length s = 2 ^ (Codec.codeK N * (s + lgv x.length + 1)) := rfl
  have hk1 : kb N x.length (s + 1) = 2 ^ (Codec.codeK N * (s + 1 + lgv x.length + 1)) := rfl
  have hB : bigB N x.length (sp x.length) =
      3 * kb N x.length (sp x.length + 1) + x.length + 3 := rfl
  have hp0 : (0 : ℤ) ≤ 0 ∧ (0 : ℤ) ≤ ((3 * kb N x.length (sp x.length + 1) : ℕ) : ℤ) :=
    ⟨le_rfl, Nat.cast_nonneg _⟩
  -- the first width computation, at radius `s`
  have hbd0 : St.Bd (bigB N x.length (sp x.length)) { St.zero with Lg := lgv x.length, s := s } :=
    by simp only [St.Bd, St.zero]; omega
  have hw1 : MReach (A (Codec.codeK N)) (orcN N) x
      (G x (bigB N x.length (sp x.length)) (3 * kb N x.length (sp x.length + 1)))
      (cf (.cp (.radX .fst) 0) { St.zero with Lg := lgv x.length, s := s } M 0)
      (cf (.iU false) (wkSt (K₀ := Codec.codeK N) .fst
        { St.zero with Lg := lgv x.length, s := s } s) M 0) :=
    wk_run .fst _ M rfl rfl rfl rfl rfl rfl hK0 hbd0 (by
      show 3 * 2 ^ (Codec.codeK N * (s + lgv x.length + 1)) ≤ _
      omega)
  set S1 := wkSt (K₀ := Codec.codeK N) .fst { St.zero with Lg := lgv x.length, s := s } s
    with hS1
  have hS1K : S1.K = kb N x.length s := rfl
  have hS1B : S1.Bs = 2 * kb N x.length s := by simp [hS1, wkSt, hk0]
  have hS1Bd : SBd (bigB N x.length (sp x.length)) (3 * kb N x.length (sp x.length + 1)) S1 :=
    ⟨by simp only [St.Bd, hS1, wkSt, St.zero]; simp; omega, by omega, by omega, by omega⟩
  -- the first search
  obtain ⟨M1, hr1, hm1, ho1, hiff1⟩ := search_run (orc := orcN N) (x := x)
    (B := bigB N x.length (sp x.length)) (P := 3 * kb N x.length (sp x.length + 1))
    (K₀ := Codec.codeK N) false S1 M rfl rfl rfl rfl rfl rfl rfl hS1Bd (fun v hv => by
      cases h : M (cell S1.Bs v)
      · rfl
      · have := hM _ h
        rw [hS1B] at this
        simp only [cell] at this
        push_cast at this
        omega)
  simp only [Bool.false_eq_true, ↓reduceIte] at hr1
  have hrr1 : rr S1 false = s := rfl
  rw [hrr1] at hr1 hiff1
  set c1 := ((Finset.range S1.K).filter (Cl (orcN N) x s S1.K)).card with hc1
  have hc1le : c1 ≤ kb N x.length s := card_filter_range_le _ _
  have hc1eq : c1 = (ExpBFS.rset N x s).card := card_cl (code_bound_le N x.length s)
  -- clearing, `c1 := c`, `s1 := s + 1`
  have hbdA : St.Bd (bigB N x.length (sp x.length)) { S1 with U := S1.K, c := c1 } := by
    simp only [St.Bd, hS1, wkSt, St.zero]; simp; omega
  have hd1 := d1_run (orc := orcN N) (x := x) (B := bigB N x.length (sp x.length))
    (P := 3 * kb N x.length (sp x.length + 1)) (K₀ := Codec.codeK N) _ M1 hbdA
  have hbdB : St.Bd (bigB N x.length (sp x.length))
      { { S1 with U := S1.K, c := c1 } with U := 0, V := 0, w := 0, K := 0, Bs := 0 } := by
    simp only [St.Bd, hS1, wkSt, St.zero]; simp; omega
  have hmv := mv_run (orc := orcN N) (x := x) (B := bigB N x.length (sp x.length))
    (P := 3 * kb N x.length (sp x.length + 1)) (K₀ := Codec.codeK N) _ M1 0 hp0 hbdB
    (by simp [hS1, wkSt, St.zero]; omega)
  have hbdC : St.Bd (bigB N x.length (sp x.length)) (st1 x.length s c1) := by
    simp only [St.Bd, St.zero, st1]; omega
  have hcp := cp_run (orc := orcN N) (x := x) (B := bigB N x.length (sp x.length))
    (P := 3 * kb N x.length (sp x.length + 1)) (K₀ := Codec.codeK N) .s1
    (st1 x.length s c1) M1 0 hp0 hbdC rfl
    (by simp only [cpDst, cpSrc]; regs; simp [St.zero, st1]; omega)
  simp only [cpDst, cpSrc, cpExit] at hcp
  regs at hcp
  have hbdD : St.Bd (bigB N x.length (sp x.length)) (st2 x.length s c1) := by
    simp only [St.Bd, St.zero, st2]; omega
  have hA2 : MReach (A (Codec.codeK N)) (orcN N) x
      (G x (bigB N x.length (sp x.length)) (3 * kb N x.length (sp x.length + 1)))
      (cf (.d1 0) { S1 with U := S1.K, c := c1 } M1 0)
      (cf (.cp (.radX .snd) 0) (st3 x.length s c1) M1 0) := by
    refine hd1.trans ?_
    refine (reach_cf hmv (st' := st1 x.length s c1)
      (by ext <;> simp [hS1, wkSt, St.zero, st1]) rfl).trans ?_
    refine (reach_cf hcp (st' := st2 x.length s c1) (by ext <;> simp [St.zero, st1, st2])
      rfl).trans ?_
    refine inc_step (r := rs1) (l' := .cp (.radX .snd) 0) rfl hbdD hp0 ?_
    regs
    refine reach_cf (MReach.refl _) ?_ rfl
    ext <;> simp [St.zero, st2, st3]
  -- the second width computation, at radius `s + 1`
  have hbd3 : St.Bd (bigB N x.length (sp x.length)) (st3 x.length s c1) := by
    simp only [St.Bd, St.zero, st3]; omega
  have hw2 : MReach (A (Codec.codeK N)) (orcN N) x
      (G x (bigB N x.length (sp x.length)) (3 * kb N x.length (sp x.length + 1)))
      (cf (.cp (.radX .snd) 0) (st3 x.length s c1) M1 0)
      (cf (.iU true) (wkSt (K₀ := Codec.codeK N) .snd (st3 x.length s c1) (s + 1)) M1 0) :=
    wk_run .snd _ M1 rfl rfl rfl rfl rfl rfl hK0 hbd3 (by
      show 3 * 2 ^ (Codec.codeK N * (s + 1 + lgv x.length + 1)) ≤ _
      omega)
  set S4 := wkSt (K₀ := Codec.codeK N) .snd (st3 x.length s c1) (s + 1) with hS4
  have hS4K : S4.K = kb N x.length (s + 1) := rfl
  have hS4B : S4.Bs = kb N x.length (s + 1) := by simp [hS4, wkSt, hk1, st3]
  have hS4Bd : SBd (bigB N x.length (sp x.length)) (3 * kb N x.length (sp x.length + 1)) S4 :=
    ⟨by simp only [St.Bd, hS4, wkSt, St.zero, st3]; simp; omega, by omega, by omega, by omega⟩
  -- the marks after the first search lie below `3 K_s`
  have hM1 : ∀ z, M1 z = true → z < ((3 * kb N x.length s : ℕ) : ℤ) := by
    intro z hz
    by_cases hin : ∃ v, v < S1.K ∧ z = cell S1.Bs v
    · obtain ⟨v, hv, rfl⟩ := hin
      rw [hS1B]; rw [hS1K] at hv
      simp only [cell]; push_cast; omega
    · push_neg at hin
      rw [ho1 z (fun v hv e => hin v hv e)] at hz
      have := hM z hz
      push_cast at this ⊢; omega
  -- the second search
  obtain ⟨M2, hr2, hm2, ho2, hiff2⟩ := search_run (orc := orcN N) (x := x)
    (B := bigB N x.length (sp x.length)) (P := 3 * kb N x.length (sp x.length + 1))
    (K₀ := Codec.codeK N) true S4 M1 rfl rfl rfl rfl rfl rfl rfl hS4Bd (fun v hv => by
      cases h : M1 (cell S4.Bs v)
      · rfl
      · have := hM1 _ h
        rw [hS4B] at this
        simp only [cell] at this
        push_cast at this
        omega)
  simp only [↓reduceIte] at hr2
  have hrr2 : rr S4 true = s + 1 := rfl
  rw [hrr2] at hr2 hiff2
  set c2 := ((Finset.range S4.K).filter (Cl (orcN N) x (s + 1) S4.K)).card with hc2
  have hc2le : c2 ≤ kb N x.length (s + 1) := card_filter_range_le _ _
  have hc2eq : c2 = (ExpBFS.rset N x (s + 1)).card := card_cl (code_bound_le N x.length (s + 1))
  -- the comparison
  have hbdE : St.Bd (bigB N x.length (sp x.length)) { S4 with U := S4.K, c := c2 } := by
    simp only [St.Bd, hS4, wkSt, St.zero, st3]; simp; omega
  refine (((hw1.trans hr1).trans hA2).trans (hw2.trans hr2)).halt ?_
  refine stepH_of rfl hbdE hp0 ?_
  simp only [astep]; regs
  have hc1' : ({ S4 with U := S4.K, c := c2 } : St).c1 = c1 := rfl
  have hS4c1 : S4.c1 = c1 := rfl
  by_cases heq : c2 = c1
  · -- equal counts: the final scan
    simp only [hS4c1, heq, ↓reduceIte]
    have hcard : (ExpBFS.rset N x s).card = (ExpBFS.rset N x (s + 1)).card := by
      rw [← hc1eq, ← hc2eq, heq]
    have hfz := fz_run (orc := orcN N) (x := x) (B := bigB N x.length (sp x.length))
      (P := 3 * kb N x.length (sp x.length + 1)) (K₀ := Codec.codeK N) _ M2
      (by rw [heq] at hbdE; exact hbdE)
    have hbd5 : St.Bd (bigB N x.length (sp x.length)) (st5 x.length s c1) := by
      simp only [St.Bd, St.zero, st5]; omega
    have hw3 : MReach (A (Codec.codeK N)) (orcN N) x
        (G x (bigB N x.length (sp x.length)) (3 * kb N x.length (sp x.length + 1)))
        (cf (.cp (.radX .fin) 0) (st5 x.length s c1) M2 0)
        (cf .fU (wkSt (K₀ := Codec.codeK N) .fin (st5 x.length s c1) s) M2 0) :=
      wk_run .fin _ M2 rfl rfl rfl rfl rfl rfl hK0 hbd5 (by
        show 3 * 2 ^ (Codec.codeK N * (s + lgv x.length + 1)) ≤ _
        omega)
    set S6 := wkSt (K₀ := Codec.codeK N) .fin (st5 x.length s c1) s with hS6
    have hS6B : S6.Bs = 2 * kb N x.length s := by simp [hS6, wkSt, hk0, st5]
    have hS6K : S6.K = kb N x.length s := rfl
    have hS6Bd : SBd (bigB N x.length (sp x.length)) (3 * kb N x.length (sp x.length + 1)) S6 :=
      ⟨by simp only [St.Bd, hS6, wkSt, St.zero, st5]; simp; omega, by omega, by omega, by omega⟩
    have hscan := fscan_run (orc := orcN N) (x := x) (B := bigB N x.length (sp x.length))
      (P := 3 * kb N x.length (sp x.length + 1)) (K₀ := Codec.codeK N) (S6.K - S6.U) S6 M2 rfl
      (by simp [hS6, wkSt, St.zero, st5]) rfl rfl rfl hS6Bd
    refine (((reach_cf hfz (st' := st5 x.length s c1)
      (by ext <;> simp [hS4, wkSt, St.zero, st3, st5]) rfl).trans
      hw3).halt ?_)
    convert hscan using 1
    -- the answer
    rw [indicator_eq_decide]
    apply decide_eq_decide.mpr
    rw [ExpBFS.mem_iff_of_card_eq hN hcard]
    have hS6U : S6.U = 0 := rfl
    have hS6K : S6.K = kb N x.length s := rfl
    have hS6s : S6.s = s := rfl
    rw [hS6U, hS6K, hS6s, hS6B]
    constructor
    · rintro ⟨u, hu, hacc⟩
      have hlt : u < kb N x.length s :=
        (ExpBFS.rcode_lt hu).trans_le (code_bound_le N x.length s)
      refine ⟨u, Nat.zero_le _, hlt, ?_, (acc_orcN s u).mpr hacc⟩
      have hout : M2 (cell (2 * kb N x.length s) u) = M1 (cell (2 * kb N x.length s) u) := by
        apply ho2
        intro v hv e
        rw [hS4B] at e
        simp only [cell] at e
        rw [hS4K] at hv
        omega
      rw [hout, ← hS1B]
      exact (hiff1 u (by rw [hS1K]; exact hlt)).mpr ((cl_iff (code_bound_le N x.length s) u).mpr hu)
    · rintro ⟨u, -, hlt, hmark, hacc⟩
      have hout : M2 (cell (2 * kb N x.length s) u) = M1 (cell (2 * kb N x.length s) u) := by
        apply ho2
        intro v hv e
        rw [hS4B] at e
        simp only [cell] at e
        rw [hS4K] at hv
        omega
      rw [hout, ← hS1B] at hmark
      refine ⟨u, (cl_iff (code_bound_le N x.length s) u).mp
        ((hiff1 u (by rw [hS1K]; exact hlt)).mp hmark), (acc_orcN s u).mp hacc⟩
  · -- different counts: the next radius
    simp only [hS4c1, heq, ↓reduceIte]
    have hslt : s < sp x.length := by
      by_contra hge
      exact heq (by rw [hc1eq, hc2eq]; exact (ExpBFS.card_rset_succ_of_le hN (by omega)).symm)
    have hnz := nz_run (orc := orcN N) (x := x) (B := bigB N x.length (sp x.length))
      (P := 3 * kb N x.length (sp x.length + 1)) (K₀ := Codec.codeK N) _ M2 hbdE
      (by simp [hS4, wkSt, St.zero, st3]; omega)
    refine (reach_cf hnz (st' := { St.zero with Lg := lgv x.length, s := s + 1 })
      (by ext <;> simp [hS4, wkSt, St.zero, st3]) rfl).halt ?_
    refine ih (sp x.length - (s + 1)) (by omega) (s + 1) M2 rfl (by omega) ?_
    intro z hz
    by_cases hin : ∃ v, v < S4.K ∧ z = cell S4.Bs v
    · obtain ⟨v, hv, rfl⟩ := hin
      rw [hS4B]; rw [hS4K] at hv
      simp only [cell]; push_cast; omega
    · push_neg at hin
      rw [ho2 z (fun v hv e => hin v hv e)] at hz
      have := hM1 z hz
      push_cast at this ⊢; omega

end ExpBFS

end Complexity.LogProg

namespace Complexity

open Turing LogProg LogProg.ExpBFS

/-- The time bound of the search machine in exponential form: with
`E = codeK N (t + 1 + lgv n + 1)` the exponent of the largest code bound, the bound
`2 ^ (C (W + logSpace n + 1)) (P + 1)²` of `Complexity.LogProg.marm_dtime` at the register
width `W = log₂ (B + 1) + 1` and memory range `P = 3 · 2 ^ E` is at most `2 ^ (c (S n + 1))`
for `c = C (a + 4) + 2a + 4`, `a = codeK N (c₀ + 3)`, when `t = c₀ S n` and
`logSpace n ≤ S n`.

**Proof sketch.** `n + 4 ≤ 2 ^ (E + 1)`, so `B + 1 < 2 ^ (E + 3)` and `W ≤ E + 3`;
`P + 1 ≤ 2 ^ (E + 2)`; `E ≤ a (S n + 1)` as `lgv n ≤ logSpace n + 1 ≤ S n + 1`. -/
private lemma time_bound (N : FinNDTM Bool) (C c₀ n Sn : ℕ) (hdom : logSpace n ≤ Sn) :
    2 ^ (C * ((Nat.log 2 (bigB N n (c₀ * Sn) + 1) + 1) + logSpace n + 1)) *
        (3 * kb N n (c₀ * Sn + 1) + 1) ^ 2 ≤
      1 * 2 ^ ((C * (Codec.codeK N * (c₀ + 3) + 4) + 2 * (Codec.codeK N * (c₀ + 3)) + 4) *
        (Sn + 1)) := by
  set K₀ := Codec.codeK N with hK₀
  have hK0 : 2 ≤ K₀ := two_le_codeK N
  set E := K₀ * (c₀ * Sn + 1 + lgv n + 1) with hE
  have hkb : kb N n (c₀ * Sn + 1) = 2 ^ E := rfl
  have hlg := lgv_le n
  have hlg' := logSpace_le_lgv n
  have hn : n + 1 ≤ 2 ^ logSpace n := Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
  have hEl : logSpace n + 1 ≤ E := by
    have : lgv n + 1 ≤ E := by
      calc lgv n + 1 ≤ 1 * (c₀ * Sn + 1 + lgv n + 1) := by omega
        _ ≤ E := Nat.mul_le_mul_right _ (by omega)
    omega
  have hpowE : 2 ^ (logSpace n + 2) ≤ 2 ^ (E + 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hn4 : n + 4 ≤ 2 ^ (E + 1) := by
    have : 2 ^ (logSpace n + 2) = 4 * 2 ^ logSpace n := by rw [pow_add]; ring
    omega
  have hE2 : 2 ^ (E + 1) = 2 * 2 ^ E := by rw [pow_succ]; ring
  have hE3 : 2 ^ (E + 3) = 8 * 2 ^ E := by rw [pow_add]; ring
  have hE2' : 2 ^ (E + 2) = 4 * 2 ^ E := by rw [pow_add]; ring
  -- the register width
  have hW : Nat.log 2 (bigB N n (c₀ * Sn) + 1) + 1 ≤ E + 3 := by
    have hlt : bigB N n (c₀ * Sn) + 1 < 2 ^ (E + 3) := by
      simp only [bigB, hkb]; omega
    have := Nat.log_lt_of_lt_pow (b := 2) (by omega) hlt
    omega
  -- the memory range
  have hP : 3 * kb N n (c₀ * Sn + 1) + 1 ≤ 2 ^ (E + 2) := by rw [hkb]; omega
  -- the exponent
  set a := K₀ * (c₀ + 3) with ha
  have hEa : E ≤ a * (Sn + 1) := by
    have : c₀ * Sn + 1 + lgv n + 1 ≤ (c₀ + 3) * (Sn + 1) := by
      have : (c₀ + 3) * (Sn + 1) = c₀ * Sn + c₀ + 3 * Sn + 3 := by ring
      omega
    calc E = K₀ * (c₀ * Sn + 1 + lgv n + 1) := rfl
      _ ≤ K₀ * ((c₀ + 3) * (Sn + 1)) := Nat.mul_le_mul_left _ this
      _ = a * (Sn + 1) := by rw [ha, mul_assoc]
  have hexp : C * ((Nat.log 2 (bigB N n (c₀ * Sn) + 1) + 1) + logSpace n + 1) + 2 * (E + 2) ≤
      (C * (a + 4) + 2 * a + 4) * (Sn + 1) := by
    have h1 : (Nat.log 2 (bigB N n (c₀ * Sn) + 1) + 1) + logSpace n + 1 ≤ (a + 4) * (Sn + 1) := by
      have : (a + 4) * (Sn + 1) = a * (Sn + 1) + 4 * Sn + 4 := by ring
      omega
    have h2 : C * ((Nat.log 2 (bigB N n (c₀ * Sn) + 1) + 1) + logSpace n + 1) ≤
        C * ((a + 4) * (Sn + 1)) := Nat.mul_le_mul_left _ h1
    have h3 : (C * (a + 4) + 2 * a + 4) * (Sn + 1) =
        C * ((a + 4) * (Sn + 1)) + 2 * (a * (Sn + 1)) + 4 * (Sn + 1) := by ring
    omega
  calc 2 ^ (C * ((Nat.log 2 (bigB N n (c₀ * Sn) + 1) + 1) + logSpace n + 1)) *
        (3 * kb N n (c₀ * Sn + 1) + 1) ^ 2
      ≤ 2 ^ (C * ((Nat.log 2 (bigB N n (c₀ * Sn) + 1) + 1) + logSpace n + 1)) *
          (2 ^ (E + 2)) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hP 2)
    _ = 2 ^ (C * ((Nat.log 2 (bigB N n (c₀ * Sn) + 1) + 1) + logSpace n + 1) + 2 * (E + 2)) := by
      rw [← pow_mul, ← pow_add, mul_comm (E + 2) 2]
    _ ≤ 2 ^ ((C * (a + 4) + 2 * a + 4) * (Sn + 1)) := Nat.pow_le_pow_right (by decide) hexp
    _ = 1 * 2 ^ ((C * (a + 4) + 2 * a + 4) * (Sn + 1)) := (one_mul _).symm

/-- **Nondeterministic space sits inside exponential time, for any space bound above the
logarithm** ([AB09, Theorem 4.2, third inclusion], without space-constructibility):
`NSPACE S ⊆ ⋃ c, DTIME (2 ^ (c (S n + 1)))` whenever `logSpace ≤ S`.

**Proof sketch.** Let `N` decide `L` in space `c₀ S`. The search machine
(`Complexity.LogProg.ExpBFS.A`) with the deciders of the input length and of `N`'s code
languages (all in `L`) answers `x ∈ L` (`setup_run`, then `iter_run` from radius `0`), with
registers below `B = 3 · 2 ^ E + |x| + 3` and its memory head in `[0, 3 · 2 ^ E]`, where
`E = codeK N (c₀ S |x| + 1 + lgv |x| + 1)`. `Complexity.LogProg.marm_dtime` gives a machine
deciding `L` in time `2 ^ (C (W + logSpace n + 1)) (P + 1)²`, which `time_bound` bounds by
`2 ^ (c (S n + 1))`. -/
theorem NSPACE_subset_exp_dtime_of_le (S : ℕ → ℕ) (hdom : ∀ n, logSpace n ≤ S n) :
    NSPACE S ⊆ ⋃ c : ℕ, DTIME fun n => 2 ^ (c * (S n + 1)) := by
  classical
  rintro L ⟨c₀, N, hN⟩
  obtain ⟨M, C, hM⟩ := marm_dtime (L := L) (A (Codec.codeK N)) .scan (decs N)
    (fun j => by
      fin_cases j
      · exact inputLenLang_mem
      · exact Codec.initLang_mem
      · exact Codec.stepLang_mem
      · exact Codec.acceptLang_mem)
    (fun n => Nat.log 2 (bigB N n (c₀ * S n) + 1) + 1) (fun n => 3 * kb N n (c₀ * S n + 1))
    (fun x => by
      have h0 := setup_run (K₀ := Codec.codeK N) (orc := orcN N) (x := x)
        (B := bigB N x.length (c₀ * S x.length)) (P := 3 * kb N x.length (c₀ * S x.length + 1))
        (orcN_len N x) (fun _ => false) (by simp only [bigB]; omega)
      have h1 := iter_run (N := N) (x := x) hN (c₀ * S x.length - 0) 0 (fun _ => false) rfl
        (Nat.zero_le _) (fun z hz => by simp at hz)
      have h := (reach_cf h0 (st' := { St.zero with Lg := lgv x.length, s := 0 })
        (by ext <;> simp [St.zero]) rfl).halt h1
      rw [St.toV_zero]
      refine h.mono fun c ⟨⟨hps, hv⟩, hp0, hpP⟩ => ⟨hps, fun r => ?_, abs_le.mpr ⟨by omega, hpP⟩⟩
      have e1 := length_bits_le_log (c.1.2.1 r + 1)
      have e2 : Nat.log 2 (c.1.2.1 r + 1) ≤ Nat.log 2 (bigB N x.length (c₀ * S x.length) + 1) :=
        Nat.log_mono_right (by have := hv r; omega)
      dsimp only
      omega)
  refine Set.mem_iUnion.mpr ⟨C * (Codec.codeK N * (c₀ + 3) + 4) +
    2 * (Codec.codeK N * (c₀ + 3)) + 4, 1, M, fun x => (hM x).mono ?_⟩
  exact time_bound N C c₀ x.length (S x.length) (hdom x.length)

end Complexity
