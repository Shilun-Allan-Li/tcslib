/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.HardCoreGL
import TCSlib.Cryptography.Asymptotic.Collections

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Goldreich–Levin inverter for collections

The collection form of [PS10, Theorem 87.3] (needed by [PS10, Theorem 104.4] and Chapter 4):
if `F` is a collection of one-way functions whose elements have encoding length `m(n)` at
generated indices, then `⟨encD_i x, r⟩` is hard-core for the padded collection
`g_i(x, r) = ⟨f_i(x), r⟩`. This file supplies the machine side for
`Collection.OneWay.glPad_hardCore` (`Asymptotic/HardCore.lean`):

* the evaluator of the bit `⟨padFin(encD_i x), r⟩` on `⟨i, ⟨encD_i x, r⟩⟩` (`padToLen`, `ipFun`);
* the recovery machine `glMachine` of `Asymptotic/HardCoreGL.lean` applied to the predictor
  pre-processed to query `⟨i, ⟨y, q⟩⟩` (`collPre`), wrapped into an inverter of the padded
  collection (`glCollMachine`);
* the per-index transfer `glColl_uprob_le` from the encoded-domain Goldreich–Levin bound
  `HardcoreBit.invProb_guessInverter_enc_pad` (`Asymptotic/GoldreichLevinDomain.lean`) to the
  inversion event of `glCollMachine`;
* the final negligibility argument `glColl_negligible`: the good set of indices
  (`HardcoreBit.half_le_uprob_threshold`), the averaging `HardcoreBit.uprob_mul_le_uexp`, and
  the polynomial arithmetic with the guess count `glKc` for a predictor of advantage
  `n^{−c}/2`.

## Main definitions

* `TCSlib.Cryptography.glKc`, `TCSlib.Cryptography.glKcBound` — the guess count for advantage
  `n^{−c}/2` and its polynomial majorant.
* `TCSlib.Cryptography.padToLen` — padding a string to the length of another.
* `TCSlib.Cryptography.glCollMachine` — the inverter of the padded collection.

## Main results

* `TCSlib.Cryptography.exists_glBitCollEvaluator` — the hard-core bit of the padded collection
  is polynomial-time computable.
* `TCSlib.Cryptography.glColl_uprob_le` — the recovery event implies the inversion event.
* `TCSlib.Cryptography.glColl_negligible` — the hardness clause of the collection form.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.5: Definition 41.1; §3.4.2–3.4.3: Theorem 87.3, Algorithm 89.6; §3.6: Theorem 104.4.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.5 (Theorem 2.3, Figure 2.5).
* [GL89] O. Goldreich, L. Levin, *A hard-core predicate for all one-way functions*, STOC 1989.
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## The guess count for a predictor of advantage `n^{−c}/2` -/

/-- The guess count `k(n) := size (8 m(n) n^{2c})`: `2 m ≤ (n^{−c}/2)² (2^k − 1)`. -/
def glKc (mP : PolyExpr) (c n : ℕ) : ℕ := Nat.size (8 * mP.eval n * n ^ (2 * c))

/-- The polynomial majorant `16 m n^{2c} + 1` of `2^{k(n)}`. -/
def glKcBound (mP : PolyExpr) (c : ℕ) : PolyExpr :=
  .add (.mul (.const 16) (.mul mP (.pow .var (2 * c)))) (.const 1)

/-- `8 m n^{2c} < 2^{k(n)}`. -/
theorem lt_two_pow_glKc (mP : PolyExpr) (c n : ℕ) :
    8 * mP.eval n * n ^ (2 * c) < 2 ^ glKc mP c n :=
  Nat.lt_size_self _

/-- `2^{k(n)} ≤ 16 m n^{2c} + 1`. -/
theorem two_pow_glKc_le (mP : PolyExpr) (c : ℕ) (n : ℕ) :
    2 ^ glKc mP c n ≤ (glKcBound mP c).eval n := by
  simp only [glKcBound, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_pow,
    PolyExpr.eval_var]
  unfold glKc
  calc 2 ^ Nat.size (8 * mP.eval n * n ^ (2 * c)) ≤ 2 * (8 * mP.eval n * n ^ (2 * c)) + 1 :=
        two_pow_size_le _
    _ = 16 * (mP.eval n * n ^ (2 * c)) + 1 := by ring

/-- The real form of the guess-count inequality for `ε = n^{−c}/2`, `n ≥ 1`. -/
theorem glKc_real (mP : PolyExpr) (c n : ℕ) (hn : 1 ≤ n) :
    2 * (mP.eval n : ℝ) ≤ (1 / (n : ℝ) ^ c / 2) ^ 2 * ((2 : ℝ) ^ glKc mP c n - 1) := by
  have h := lt_two_pow_glKc mP c n
  have hcast : (8 * (mP.eval n : ℝ) * (n : ℝ) ^ (2 * c)) + 1 ≤ (2 : ℝ) ^ glKc mP c n := by
    exact_mod_cast h
  have hnR : (0 : ℝ) < (n : ℝ) ^ c := pow_pos (by exact_mod_cast hn) c
  have hsq : (1 / (n : ℝ) ^ c / 2) ^ 2 = 1 / (4 * (n : ℝ) ^ (2 * c)) := by
    rw [pow_mul]; field_simp; ring
  rw [hsq, one_div, inv_mul_eq_div, le_div_iff₀ (by positivity)]
  nlinarith

/-- The guess count is positive when the block length is (`n ≥ 1`). -/
theorem glKc_pos_or (mP : PolyExpr) (c n : ℕ) (hn : 1 ≤ n) :
    0 < 2 ^ glKc mP c n - 1 ∨ mP.eval n = 0 := by
  rcases Nat.eq_zero_or_pos (mP.eval n) with hm | hm
  · exact Or.inr hm
  · left
    have h := lt_two_pow_glKc mP c n
    have : 0 < 8 * mP.eval n * n ^ (2 * c) := by positivity
    omega

/-! ## Padding and the bit evaluator -/

/-- Padding or truncating the first component of a pair to the length of the second:
`⟨a, b⟩ ↦ (a ++ 0^{|b|}).take |b|`, the string `ofFn (padFin |b| a)`. -/
def padToLen (z : List Bool) : List Bool :=
  (pairFstD z ++ List.zipWith xor (pairSndD z) (pairSndD z)).take (pairSndD z).length

/-- Padding is polynomial-time. -/
theorem padToLen_poly : PolyTimeComputable padToLen :=
  takeLen_poly polyTimeComputable_pairSndD
    (polyTimeComputable_pairFstD.append (zipXor_poly polyTimeComputable_pairSndD polyTimeComputable_pairSndD))

/-- Padding `a` to the length of an encoded `L`-bit string encodes `padFin L a`. -/
theorem padToLen_pairEncode_ofFn (a : List Bool) {L : ℕ} (ρ : Fin L → Bool) :
    padToLen (pairEncode a (List.ofFn ρ)) = List.ofFn (padFin L a) := by
  simp only [padToLen, pairFstD_pairEncode, pairSndD_pairEncode, List.length_ofFn]
  refine List.ext_getElem (by simp) fun j hj₁ hj₂ => ?_
  simp only [List.length_ofFn] at hj₂
  simp only [List.getElem_take, List.getElem_ofFn, padFin, List.getD_eq_getElem?_getD]
  by_cases h : j < a.length
  · rw [List.getElem_append_left h, List.getElem?_eq_getElem h]
    rfl
  · rw [List.getElem_append_right (by omega), List.getElem?_eq_none (by omega), List.getElem_zipWith,
      Bool.xor_self]
    rfl

/-- The encoding of `padFin L w` is `w` when `|w| = L`. -/
theorem ofFn_padFin_of_length {L : ℕ} {w : List Bool} (hw : w.length = L) :
    List.ofFn (padFin L w) = w := by
  refine List.ext_getElem (by simp [hw]) fun j hj₁ hj₂ => ?_
  simp [padFin, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj₂]

/-- **The evaluator of the hard-core bit of the padded collection** `⟨padFin(encD_i x), r⟩` on
`⟨i, ⟨encD_i x, r⟩⟩` [PS10, Theorem 87.3, collection form, efficiency clause]. -/
theorem exists_glBitCollEvaluator (F : Collection) :
    ∃ H : List Bool → List Bool, PolyTimeComputable H ∧
      ∀ i (x : F.D i) {L : ℕ} (ρ : Fin L → Bool),
        H (pairEncode i (pairEncode (F.encD i x) (List.ofFn ρ))) =
          [HardcoreBit.ip (padFin L (F.encD i x)) ρ] := by
  refine ⟨fun w => ipFun (pairEncode (padToLen (pairSndD w)) (pairSndD (pairSndD w))),
    ptcComp (g := ipFun) ipFun_poly ((ptcComp (g := padToLen) padToLen_poly polyTimeComputable_pairSndD).pairEncode
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)), fun i x L ρ => ?_⟩
  simp only [pairSndD_pairEncode, padToLen_pairEncode_ofFn, ipFun_ofFn]

/-- The inner product is invariant under transport along an equality of lengths (private copy
of `HardcoreBit.ip_cast`, `Asymptotic/HardCorePermutation.lean`). -/
private theorem ip_cast' {k m : ℕ} (h : k = m) (x r : Fin k → Bool) :
    HardcoreBit.ip x r =
      HardcoreBit.ip (fun j => x (Fin.cast h.symm j)) (fun j => r (Fin.cast h.symm j)) := by
  subst h; rfl

/-! ## The predictor pre-processing and the inverter -/

/-- The pre-processing of the collection predictor: `⟨⟨i, y⟩, q⟩ ↦ ⟨i, ⟨y, q⟩⟩`. -/
def collPre (z : List Bool) : List Bool :=
  pairEncode (pairFstD (pairFstD z)) (pairEncode (pairSndD (pairFstD z)) (pairSndD z))

/-- The pre-processing is polynomial-time. -/
theorem collPre_poly : PolyTimeComputable collPre :=
  (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD).pairEncode
    ((polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD).pairEncode polyTimeComputable_pairSndD)

/-- The predictor queried by the recovery machine on `⟨⟨i, y⟩, q⟩` is the collection
distinguisher `A(1^n, ⟨i, ⟨y, q⟩⟩)`. -/
theorem glPredictorOf_precomp_coll (A : NUPPT) (n m : ℕ) (i y : List Bool) (q : Fin m → Bool)
    (c : A.Coins n) :
    glPredictorOf (A.precomp collPre_poly) n m (fun y : List Bool => pairEncode i y) (y, q) c =
      A.distinguisherL n (pairEncode i (pairEncode y (List.ofFn q))) c := by
  simp only [glPredictorOf, NUPPT.runAtL_precomp, collPre, pairFstD_pairEncode, pairSndD_pairEncode,
    NUPPT.distinguisherL, NUPPT.runAt_eq]

/-- The pre-processing of the collection inverter: on the view of `⟨1^n, ⟨i, ⟨y, r⟩⟩⟩`, the
string `⟨i, y⟩`. -/
def glCollPre (v : List Bool) : List Bool :=
  pairEncode (pairFstD (NUPPT.inArg v)) (pairFstD (pairSndD (NUPPT.inArg v)))

/-- The pre-processing is polynomial-time. -/
theorem glCollPre_poly : PolyTimeComputable glCollPre :=
  (polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg).pairEncode
    (polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg))

/-- The post-processing of the collection inverter: `⟨answer, r⟩`. -/
def glCollPost (v : List Bool) : List Bool :=
  pairEncode (pairSndD v) (pairSndD (pairSndD (NUPPT.inArg (pairFstD v))))

/-- The post-processing is polynomial-time. -/
theorem glCollPost_poly : PolyTimeComputable glCollPost :=
  polyTimeComputable_pairSndD.pairEncode (polyTimeComputable_pairSndD.comp
    (polyTimeComputable_pairSndD.comp (NUPPT.polyTimeComputable_inArg.comp polyTimeComputable_pairFstD)))

/-- **The inverter of the padded collection** [PS10, Algorithm 89.6, collection form]: the
recovery machine for the pre-processed predictor, run on `⟨i, y⟩`, its answer paired with `r`. -/
noncomputable def glCollMachine (A : NUPPT) (mP K : PolyExpr) (k : ℕ → ℕ)
    (hk : ∀ n, 2 ^ k n ≤ K.eval n) : NUPPT :=
  (glMachine (A.precomp collPre_poly) mP K k hk).wrap glCollPre_poly glCollPost_poly (fun _ => [])
    (.const 0) (fun _ => by simp) (.const 0)

/-- The collection inverter on `⟨i, ⟨y, r⟩⟩` with coins `c` returns `⟨recovery(⟨i, y⟩), r⟩`. -/
theorem glCollMachine_runAt (A : NUPPT) (mP K : PolyExpr) (k : ℕ → ℕ) (hk : ∀ n, 2 ^ k n ≤ K.eval n)
    (n : ℕ) (i y rs : List Bool) (c : (glMachine (A.precomp collPre_poly) mP K k hk).Coins n)
    (r' : (glCollMachine A mP K k hk).Coins n) (hr' : List.ofFn r' = List.ofFn c) :
    (glCollMachine A mP K k hk).runAt n (pairEncode i (pairEncode y rs)) r' =
      pairEncode ((glMachine (A.precomp collPre_poly) mP K k hk).runAt n (pairEncode i y) c) rs := by
  unfold glCollMachine
  rw [NUPPT.runAt_wrap (glMachine (A.precomp collPre_poly) mP K k hk) glCollPre_poly glCollPost_poly
    _ _ _ (.const 0) n _ rfl (fun _ : Fin 0 => false) c r' (by rw [hr']; rfl)]
  simp [glCollPre, glCollPost]

/-! ## The per-index transfer -/

/-- **The recovery event implies the inversion event**: at an index `i` whose elements have
encoding length `m(n)`, if the recovery procedure (with the collection predictor) outputs
`padFin(encD_i x)` on `f_i(x)`, the collection inverter inverts `g_i(x, r) = ⟨f_i(x), r⟩`.

**Proof sketch.** Reindex the padding by `L = m(n)` and the coins of the inverter by
`glCoinsEquiv` (the unread coins dropped by `uprob_fst`); pointwise, `glCollMachine_runAt`,
`glMachine_runAt_guessRecover` and `glPredictorOf_precomp_coll` identify the inverter's answer
with `⟨ofFn (guessRecover …), r⟩`, which is `⟨encD_i x, r⟩` (`ofFn_padFin_of_length`) and decodes
to `(x, r)` (`glPadDecode_pairEncode_ofFn`, `decD_encD`). -/
theorem glColl_uprob_le (F : Collection) (mP K : PolyExpr) (k : ℕ → ℕ)
    (hk : ∀ n, 2 ^ k n ≤ K.eval n) (A : NUPPT) (n : ℕ) (i : List Bool) (L : ℕ)
    (hL : L = mP.eval n) (hM : 0 < 2 ^ k n - 1 ∨ mP.eval n = 0)
    (henc : ∀ x : F.D i, (F.encD i x).length = mP.eval n) :
    uprob (fun z : (F.D i × (Fin (mP.eval n) → Bool)) ×
        HardcoreBit.GuessCoins (mP.eval n) (k n) (A.Coins n) =>
      HardcoreBit.guessRecover
        (fun (p : List Bool × (Fin (mP.eval n) → Bool)) (c : A.Coins n) =>
          A.distinguisherL n (pairEncode i (pairEncode p.1 (List.ofFn p.2))) c) (k n)
        (F.f i z.1.1) z.2 = padFin (mP.eval n) (F.encD i z.1.1)) ≤
    uprob (fun z : (F.D i × (Fin L → Bool)) × (glCollMachine A mP K k hk).Coins n =>
      ∃ x', glPadDecode F i L ((glCollMachine A mP K k hk).runAt n
          (pairEncode i (pairEncode (F.f i z.1.1) (List.ofFn z.1.2))) z.2) = some x' ∧
        pairEncode (F.f i x'.1) (List.ofFn x'.2) = pairEncode (F.f i z.1.1) (List.ofFn z.1.2)) := by
  have hpred : (fun (p : List Bool × (Fin (mP.eval n) → Bool)) (c : A.Coins n) =>
      A.distinguisherL n (pairEncode i (pairEncode p.1 (List.ofFn p.2))) c) =
      glPredictorOf (A.precomp collPre_poly) n (mP.eval n) (fun y : List Bool => pairEncode i y) := by
    funext p c
    obtain ⟨y, q⟩ := p
    exact (glPredictorOf_precomp_coll A n (mP.eval n) i y q c).symm
  rw [hpred]
  have hcoins : (glCollMachine A mP K k hk).coinLen n = (glCoins mP K (A.precomp collPre_poly)).eval n := by
    simp [glCollMachine, NUPPT.coinLen]
  let eC : HardcoreBit.GuessCoins (mP.eval n) (k n) ((A.precomp collPre_poly).Coins n) ×
      (Fin ((glCoins mP K (A.precomp collPre_poly)).eval n - glNeed (A.precomp collPre_poly) mP k n) → Bool) ≃
      (glCollMachine A mP K k hk).Coins n :=
    (glCoinsEquiv (A.precomp collPre_poly) n (mP.eval n) (k n) _ (glNeed_le (A.precomp collPre_poly) mP K k hk n)).trans (finCastEquiv hcoins.symm)
  haveI : Nonempty (Fin ((glCoins mP K (A.precomp collPre_poly)).eval n - glNeed (A.precomp collPre_poly) mP k n) → Bool) := ⟨fun _ => false⟩
  refine le_of_eq_of_le (uprob_fst (β := Fin ((glCoins mP K (A.precomp collPre_poly)).eval n - glNeed (A.precomp collPre_poly) mP k n) → Bool)
    _).symm ?_
  refine le_of_le_of_eq ?_ (uprob_comp_equiv ((Equiv.prodAssoc (F.D i × (Fin (mP.eval n) → Bool))
    (HardcoreBit.GuessCoins (mP.eval n) (k n) ((A.precomp collPre_poly).Coins n))
    (Fin ((glCoins mP K (A.precomp collPre_poly)).eval n - glNeed (A.precomp collPre_poly) mP k n) → Bool)).trans
    (((Equiv.refl (F.D i)).prodCongr (finCastEquiv hL.symm)).prodCongr eC)) _)
  refine uprob_mono fun w hw => ?_
  obtain ⟨⟨⟨x, ρ⟩, g⟩, ex⟩ := w
  simp only [Equiv.trans_apply, Equiv.prodAssoc_apply, Equiv.prodCongr_apply, Prod.map_apply,
    Equiv.coe_refl, id] at hw ⊢
  rw [glCollMachine_runAt A mP K k hk n i (F.f i x) (List.ofFn (finCastEquiv hL.symm ρ))
      (glCoinsEquiv (A.precomp collPre_poly) n (mP.eval n) (k n) _ (glNeed_le (A.precomp collPre_poly) mP K k hk n) (g, ex)) _
      (by simp only [eC, Equiv.trans_apply]; exact ofFn_finCastEquiv _ _),
    glMachine_runAt_guessRecover (A.precomp collPre_poly) mP K k hk n hM (fun y : List Bool => pairEncode i y) (F.f i x) g ex,
    hw, ofFn_padFin_of_length (henc x), glPadDecode_pairEncode_ofFn, F.decD_encD]
  exact ⟨(x, finCastEquiv hL.symm ρ), rfl, rfl⟩


/-! ## The hardness clause -/

/-- **The hardness clause of the collection form of Goldreich–Levin** [PS10, Theorem 87.3,
collection form]: if every inverter `B` of the padded collection `g_i(x, r) = ⟨f_i(x), r⟩` (with
padding length `L n r = m(n)` and decoder `glPadDecode`) has negligible success, then the
advantage `max 0 (Pr[A predicts ⟨padFin(encD_i x), r⟩] − 1/2)` of any predictor `A` is
negligible.

**Proof sketch.** By contradiction: `not_negligible_iff` gives `c` with `1/2 + n^{−c} ≤ uexp q`
for infinitely many `n`, `q r` the per-index success. The good indices
`{r | 1/2 + n^{−c}/2 ≤ q r}` have probability `≥ n^{−c}/2`
(`HardcoreBit.half_le_uprob_threshold`). At a good index the prediction hypothesis, transported
to padding length `m(n)` (`finCastEquiv`, `ip_cast'`), feeds
`HardcoreBit.invProb_guessInverter_enc_pad` with the guess count `glKc` (`glKc_real`), so the
recovery procedure outputs `padFin(encD_i x)` with probability `≥ ε/(4·2^k)`, `ε = n^{−c}/2`;
`glColl_uprob_le` turns this into the inversion event of `glCollMachine`. Averaging over the
good indices (`HardcoreBit.uprob_mul_le_uexp`) gives inversion probability
`≥ ε²/(4·2^k) ≥ n^{−(2c+d+1)}` (`two_pow_glKc_le`, `PolyExpr.eval_le`) infinitely often,
contradicting `hhard (glCollMachine …)`. -/
theorem glColl_negligible (F : Collection) (mP : PolyExpr) (L : ∀ n, F.gen.Coins n → ℕ)
    (hL : ∀ n r, L n r = mP.eval n)
    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)),
      (F.encD (F.index n r) x).length = mP.eval n)
    (A : NUPPT)
    (hhard : ∀ B : NUPPT, Negligible fun n => uexp fun r : F.gen.Coins n =>
      uprob fun z : (F.D (F.index n r) × (Fin (L n r) → Bool)) × B.Coins n =>
        ∃ x', glPadDecode F (F.index n r) (L n r) (B.runAt n (pairEncode (F.index n r)
            (pairEncode (F.f (F.index n r) z.1.1) (List.ofFn z.1.2))) z.2) = some x' ∧
          pairEncode (F.f (F.index n r) x'.1) (List.ofFn x'.2) =
            pairEncode (F.f (F.index n r) z.1.1) (List.ofFn z.1.2)) :
    Negligible fun n => max 0 (uexp (fun r : F.gen.Coins n =>
      uprob fun z : (F.D (F.index n r) × (Fin (L n r) → Bool)) × A.Coins n =>
        A.distinguisherL n (pairEncode (F.index n r)
          (pairEncode (F.f (F.index n r) z.1.1) (List.ofFn z.1.2))) z.2 =
          HardcoreBit.ip (padFin (L n r) (F.encD (F.index n r) z.1.1)) z.1.2) - 1 / 2) := by
  by_contra hneg
  obtain ⟨c, hc⟩ := not_negligible_iff.mp hneg
  set K := glKcBound mP c with hK
  set B := glCollMachine A mP K (glKc mP c) (two_pow_glKc_le mP c) with hB
  obtain ⟨C, d, hCd⟩ := K.eval_le
  obtain ⟨n₀, hn₀⟩ := hhard B (2 * c + d + 1)
  obtain ⟨n, hn, hgap⟩ := hc (max n₀ (max 1 (16 * C * 2 ^ d)))
  have hn1 : 1 ≤ n := le_of_max_le_left (le_of_max_le_right hn)
  have hnC : 16 * C * 2 ^ d ≤ n := le_of_max_le_right (le_of_max_le_right hn)
  haveI : Nonempty (F.gen.Coins n) := ⟨fun _ => false⟩
  set q : F.gen.Coins n → ℝ := fun r =>
    uprob fun z : (F.D (F.index n r) × (Fin (L n r) → Bool)) × A.Coins n =>
      A.distinguisherL n (pairEncode (F.index n r)
        (pairEncode (F.f (F.index n r) z.1.1) (List.ofFn z.1.2))) z.2 =
        HardcoreBit.ip (padFin (L n r) (F.encD (F.index n r) z.1.1)) z.1.2 with hq
  have hε0 : (0 : ℝ) < 1 / (n : ℝ) ^ c := by positivity
  have hpred : 1 / 2 + 1 / (n : ℝ) ^ c ≤ uexp q := by
    rw [abs_of_nonneg (le_max_left _ _)] at hgap
    rcases le_or_gt (uexp q - 1 / 2) 0 with hle | hlt
    · rw [max_eq_left hle] at hgap; linarith
    · rw [max_eq_right hlt.le] at hgap; linarith
  have hgood := HardcoreBit.half_le_uprob_threshold q (fun r => uprob_le_one _) (by norm_num)
    hε0.le hpred
  set ε : ℝ := 1 / (n : ℝ) ^ c / 2 with hε
  have hεpos : 0 < ε := by positivity
  have hkR := glKc_real mP c n hn1
  have hM := glKc_pos_or mP c n hn1
  set inner : F.gen.Coins n → ℝ := fun r =>
    uprob fun z : (F.D (F.index n r) × (Fin (L n r) → Bool)) × B.Coins n =>
      ∃ x', glPadDecode F (F.index n r) (L n r) (B.runAt n (pairEncode (F.index n r)
          (pairEncode (F.f (F.index n r) z.1.1) (List.ofFn z.1.2))) z.2) = some x' ∧
        pairEncode (F.f (F.index n r) x'.1) (List.ofFn x'.2) =
          pairEncode (F.f (F.index n r) z.1.1) (List.ofFn z.1.2) with hinnerdef
  have hinner : ∀ r : F.gen.Coins n, 1 / 2 + ε ≤ q r →
      ε / (4 * 2 ^ glKc mP c n) ≤ inner r := by
    intro r hr
    have hq' : 1 / 2 + ε ≤ uprob fun z : (F.D (F.index n r) × (Fin (mP.eval n) → Bool)) × A.Coins n =>
        (fun (p : List Bool × (Fin (mP.eval n) → Bool)) (cc : A.Coins n) =>
          A.distinguisherL n (pairEncode (F.index n r) (pairEncode p.1 (List.ofFn p.2))) cc)
          (F.f (F.index n r) z.1.1, z.1.2) z.2 =
        HardcoreBit.ip (padFin (mP.eval n) (F.encD (F.index n r) z.1.1)) z.1.2 := by
      refine hr.trans (le_of_eq ?_)
      rw [hq]
      refine (OneWay.uprob_congr fun z => ?_).trans (uprob_comp_equiv
        (((Equiv.refl (F.D (F.index n r))).prodCongr (finCastEquiv (hL n r))).prodCongr
          (Equiv.refl (A.Coins n))) _)
      obtain ⟨⟨x, ρ⟩, cc⟩ := z
      simp only [Equiv.prodCongr_apply, Prod.map_apply, Equiv.coe_refl, id, ofFn_finCastEquiv]
      rw [ip_cast' (hL n r) (padFin (L n r) (F.encD (F.index n r) x)) ρ]
      exact Iff.rfl
    have hGL := HardcoreBit.invProb_guessInverter_enc_pad
      (fun x : F.D (F.index n r) => padFin (mP.eval n) (F.encD (F.index n r) x)) (F.f (F.index n r))
      (fun (p : List Bool × (Fin (mP.eval n) → Bool)) (cc : A.Coins n) =>
        A.distinguisherL n (pairEncode (F.index n r) (pairEncode p.1 (List.ofFn p.2))) cc)
      (k := glKc mP c n) (ε := ε) hεpos hkR hq'
    have htr := glColl_uprob_le F mP K (glKc mP c) (two_pow_glKc_le mP c) A n (F.index n r)
      (L n r) (hL n r) hM (henc n r)
    exact hGL.trans htr
  have hbound := HardcoreBit.uprob_mul_le_uexp (G := fun r => 1 / 2 + ε ≤ q r) (q := inner)
    (fun r => uprob_nonneg _) hinner
  have hsmall := hn₀ n (le_of_max_le_left hn)
  have hnn : 0 ≤ uexp inner := by
    unfold uexp
    exact div_nonneg (Finset.sum_nonneg fun r _ => uprob_nonneg _) (Nat.cast_nonneg _)
  rw [abs_of_nonneg hnn] at hsmall
  have hprod : ε * (ε / (4 * 2 ^ glKc mP c n)) ≤ uexp inner :=
    (mul_le_mul_of_nonneg_right hgood (by positivity)).trans hbound
  have h2k : ((2 : ℝ) ^ glKc mP c n) ≤ (C : ℝ) * ((n : ℝ) + 1) ^ d := by
    exact_mod_cast (two_pow_glKc_le mP c n).trans (hCd n)
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnCR : (16 : ℝ) * C * 2 ^ d ≤ n := by exact_mod_cast hnC
  have hpow : ((n : ℝ) + 1) ^ d ≤ (2 * (n : ℝ)) ^ d :=
    pow_le_pow_left₀ (by positivity) (by linarith) d
  have hεsq : ε * (ε / (4 * 2 ^ glKc mP c n)) = 1 / (16 * (n : ℝ) ^ (2 * c) * 2 ^ glKc mP c n) := by
    rw [hε, pow_mul]
    field_simp
    ring
  have hlow : 1 / (n : ℝ) ^ (2 * c + d + 1) ≤ 1 / (16 * (n : ℝ) ^ (2 * c) * 2 ^ glKc mP c n) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, one_mul]
    calc 16 * (n : ℝ) ^ (2 * c) * 2 ^ glKc mP c n ≤ 16 * (n : ℝ) ^ (2 * c) * (C * (2 * (n : ℝ)) ^ d) := by
          gcongr
          exact h2k.trans (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _))
      _ = (n : ℝ) ^ (2 * c) * (n : ℝ) ^ d * (16 * C * 2 ^ d) := by ring
      _ ≤ (n : ℝ) ^ (2 * c) * (n : ℝ) ^ d * n := by gcongr
      _ = (n : ℝ) ^ (2 * c + d + 1) := by ring
  linarith

end TCSlib.Cryptography
