/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.HardCoreGLColl
import TCSlib.Cryptography.Asymptotic.HardCoreLemmas

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Goldreich–Levin for collections

The collection form of the Goldreich–Levin theorem [PS10, Theorem 87.3], the one the text uses
for [PS10, Theorem 104.4] and Chapter 4: for a collection `{f_i : D_i → R_i}` of one-way
functions, the padded collection `g_i(x, r) = (f_i(x), r)` is a collection of one-way functions
and `⟨x, r⟩` is hard-core for it; and the same for collections of permutations and of trapdoor
permutations. The machine side is `Asymptotic/HardCoreGLColl.lean` and
`Asymptotic/HardCoreLemmas.lean`. (Moved out of `Asymptotic/HardCore.lean` for size, gate 03c,
finding 11; the declarations, their names and statements are unchanged, and `HardCore.lean`
imports this file, so its importers see them as before.)

**Deviation:** [PS10, Theorem 87.3] for collections (unnumbered): the padded collection
`Collection.glPad F m` pads each element by `|encD_i(default)|` uniform bits; its one-wayness
and hard-core theorems assume length-regular encodings at generated indices
(`∀ n r x, |encD_{index n r} x| = m(n)`), which the text's "`|x| = |r|`" presupposes, at the
cost stated at `Collection.glPad` (no candidate of the library satisfies it as parametrized;
gate 03c, finding 3, ruling G3-7c). Its hard-core proof uses the encoded-domain
Goldreich–Levin lemma `HardcoreBit.invProb_guessInverter_enc_pad`
(`Asymptotic/GoldreichLevinDomain.lean`): the cube lemma does not transfer to a domain `D_i`
whose encoding is a strict subset of the cube (run-3 audit P4-2).

## Main definitions

* `TCSlib.Cryptography.Collection.glPad`, `TCSlib.Cryptography.Collection.glBit` — the padded
  collection `g_i(x, r) = (f_i(x), r)` and the predicate `⟨x, r⟩`.
* `TCSlib.Cryptography.PermCollection.glPad`, `TCSlib.Cryptography.TrapdoorCollection.glPad` —
  the padded collection of (trapdoor) permutations.

## Main results

* `TCSlib.Cryptography.goldreich_levin_coll`, `TCSlib.Cryptography.Collection.OneWay.glPad`,
  `TCSlib.Cryptography.Collection.OneWay.glPad_hardCore` [PS10, Theorem 87.3, collection form].
* `TCSlib.Cryptography.PermCollection.OneWay.glPad`,
  `TCSlib.Cryptography.PermCollection.OneWay.glPad_hardCore`,
  `TCSlib.Cryptography.TrapdoorCollection.OneWay.glPad`,
  `TCSlib.Cryptography.TrapdoorCollection.OneWay.glPad_hardCore` — the (trapdoor) permutation
  forms, for [PS10, Theorem 104.4].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.5: Definition 41.1; §2.10: Definition 55.1; §2.11: Definition 56.1; §3.4.2–3.4.3:
  Theorem 87.3; §3.10: Theorem 104.4.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.5 (Theorem 2.3).
* [GL89] O. Goldreich, L. Levin, *A hard-core predicate for all one-way functions*, STOC 1989.
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## Goldreich–Levin for collections [PS10, Theorem 87.3, collection form] -/

namespace Collection

variable (F : Collection)

/-- The **padded collection** `g_i(x, r) = (f_i(x), r)` of [PS10, Theorem 87.3] for a
collection `{f_i : D_i → R_i}` whose elements have encoding length `m(n)` at the indices
generated at parameter `n` (`henc`): the domain `D'_i = D_i × {0,1}^{|encD_i(default)|}` (the
padding has the length of the encoded elements), elements encoded as `⟨encD_i x, r⟩`, the
same index generator `Gen`, the sampler `Sample'(1^n, i) = ⟨Sample(1^n, i), r⟩` with `m(n)`
fresh coins `r`, and the evaluator `⟨i, ⟨x, r⟩⟩ ↦ ⟨eval ⟨i, x⟩, r⟩`. The sampler's outputs
decode (`sample_spec`): the first component by `F.sample_spec`, the padding because it has
exactly `m(n) = |encD_i(default)|` bits by `henc`.

Repair (run-3 audit P3-1): the hypothesis `henc` (previously carried by the theorems only) is
now an argument of the definition, since without it the padding of the sampled string need not
have the length the decoder expects and `Collection.sample_spec` would fail.

**Deviation:** the text's "`|x| = |r|`" presupposes that all elements of `D_i` have the same
encoding length; `glPad` assumes `|encD_i x| = m(n)` at generated indices (`henc`). Cost (gate
03c, finding 3; ruling G3-7c): a non-constant `PolyExpr` is strictly increasing, so an index
generated at two parameters forces `m` constant, and no candidate of the library satisfies `henc`
as parametrized (`rsaTrapdoor`: `2·max(n, 2)`-bit elements; `rabinBlumTrapdoor`: `2·max(n, 3)`;
`expCollection`: `dlDefaultIndex` below `n₀`). A per-index form (`|encD_i x| = |encD_i default|
≤ m(n)`) would admit them; it is not formalized. -/
noncomputable def glPad (m : PolyExpr)
    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n) :
    Collection where
  D i := F.D i × (Fin (F.encD i default).length → Bool)
  encD i z := pairEncode (F.encD i z.1) (List.ofFn z.2)
  decD i w := match pairDecode w with
    | some (a, b) => match F.decD i a, decodeFin (F.encD i default).length b with
      | some x, some r => some (x, r)
      | _, _ => none
    | none => none
  decD_encD i z := by simp [pairDecode_pairEncode, F.decD_encD, decodeFin_ofFn]
  encD_decD i w z h := by
    rcases hw : pairDecode w with _ | ⟨a, b⟩
    · simp [hw] at h
    cases ha : F.decD i a <;> cases hb : decodeFin (F.encD i default).length b <;> simp [hw, ha, hb] at h
    rw [eq_pairEncode_of_pairDecode w a b hw, ← h, F.encD_decD i a _ ha, ofFn_of_decodeFin_eq_some hb]
  f i z := pairEncode (F.f i z.1) (List.ofFn z.2)
  gen := F.gen
  gen_uniform := F.gen_uniform
  sample := NUPPT.ofPolyTimeUniform (glPadSampleFun_poly F) (.add F.sample.coins m)
  sample_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  eval w := pairEncode (F.eval (pairEncode (pairFstD w) (pairFstD (pairSndD w))))
    (pairSndD (pairSndD w))
  eval_poly := (F.eval_poly.comp (polyTimeComputable_pairFstD.pairEncode
    (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD))).pairEncode
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  eval_spec i z := by simp [F.eval_spec]
  sample_spec n r s := by
    obtain ⟨⟨s₁, s₂⟩, hs⟩ := (Fin.appendEquiv (F.sample.coins.eval n) (m.eval n)).surjective
      (NUPPT.coinsEquiv_ofPolyTimeUniform (glPadSampleFun_poly F) (.add F.sample.coins m) n s)
    have hofn : List.ofFn s = List.ofFn s₁ ++ List.ofFn s₂ := by
      rw [← NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn (glPadSampleFun_poly F)
        (.add F.sample.coins m) n s, ← hs]
      exact List.ofFn_fin_append s₁ s₂
    have hA : (List.ofFn s).take (F.sample.coinLen n) = List.ofFn s₁ := by
      rw [hofn, NUPPT.coinLen_eq, List.take_left' List.length_ofFn]
    have hB : (List.ofFn s).drop (F.sample.coinLen n) = List.ofFn s₂ := by
      rw [hofn, NUPPT.coinLen_eq, List.drop_left' List.length_ofFn]
    have h₁ : List.ofFn ((NUPPT.coinsEquivPoly (A := F.sample) rfl n).symm s₁) = List.ofFn s₁ :=
      NUPPT.coinsEquivPoly_symm_ofFn rfl n s₁
    obtain ⟨x, hx, hev⟩ := F.sample_spec n r ((NUPPT.coinsEquivPoly (A := F.sample) rfl n).symm s₁)
    have hL : (F.encD (pairFstD (F.gen.runAt n [] r)) default).length = m.eval n := by
      have := henc n r default
      rwa [Collection.index_eq] at this
    have hs₂ : List.ofFn s₂ = List.ofFn
        fun j : Fin (F.encD (pairFstD (F.gen.runAt n [] r)) default).length => s₂ (Fin.cast hL j) :=
      List.ofFn_congr hL.symm s₂
    refine ⟨(x, fun j => s₂ (Fin.cast hL j)), ?_, ?_⟩
    · simp only [glPadSample_runAt, hA, hB, pairDecode_pairEncode, ← h₁, ← NUPPT.runAt_eq, hx, hs₂,
        decodeFin_ofFn]
    · simp only [glPadSample_runAt, hA, hB, pairFstD_pairEncode, pairSndD_pairEncode, ← h₁,
        ← NUPPT.runAt_eq, hev, hs₂]

/-- The predicate `h_i(x, r) = ⟨x, r⟩` for the padded collection: the inner product of the
encoding of `x` (padded or truncated to the padding length) with `r`. -/
def glBit : ∀ i, F.D i × (Fin (F.encD i default).length → Bool) → Bool :=
  fun i z => HardcoreBit.ip (padFin _ (F.encD i z.1)) z.2

/-- Unfolding: `h_i(x, r)` is the inner product `⟨padFin(encD_i x), r⟩`, the encoding of `x`
padded or truncated to the padding length `|encD_i(default)|`. -/
theorem glBit_eq (i : List Bool) (z : F.D i × (Fin (F.encD i default).length → Bool)) :
    F.glBit i z = HardcoreBit.ip (padFin _ (F.encD i z.1)) z.2 := rfl

variable {F} in
/-- Unfolding: the padded collection keeps the index generator. -/
theorem glPad_gen (m : PolyExpr)
    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n) :
    (F.glPad m henc).gen = F.gen := rfl

variable {F} in
/-- Unfolding: `g_i(x, r) = ⟨f_i(x), r⟩`. -/
theorem glPad_f (m : PolyExpr)
    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n)
    (i : List Bool) (z : (F.glPad m henc).D i) :
    (F.glPad m henc).f i z = pairEncode (F.f i z.1) (List.ofFn z.2) := rfl

variable {F} in
/-- Unfolding: the sampler of the padded collection runs `Sample(1^n, i)` on its first
`|Sample's coins|` coins and appends the remaining coins. -/
theorem glPad_sample_runAtL (m : PolyExpr)
    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n)
    (n : ℕ) (i r : List Bool) :
    (F.glPad m henc).sample.runAtL n i r =
      pairEncode (F.sample.runAtL n i (r.take (F.sample.coinLen n))) (r.drop (F.sample.coinLen n)) := by
  simp only [glPad, NUPPT.runAtL, NUPPT.ofPolyTimeUniform, NUPPT.output_ofPolyTime,
    glPadSampleFun, NUPPT.inParam, NUPPT.inArg, NUPPT.inCoins, NUPPT.advInput, NUPPT.layout,
    pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate, F.sample_uniform n,
    NUPPT.coinLen]

variable {F} in
/-- Unfolding: the decoder of the padded collection is `glPadDecode` at the padding length
`|encD_i(default)|` (propositional: the two `match` expressions are compiled separately). -/
theorem glPad_decD_eq (m : PolyExpr)
    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n)
    (i : List Bool) : (F.glPad m henc).decD i = glPadDecode F i (F.encD i default).length := by
  funext w
  unfold Collection.glPad glPadDecode
  dsimp only
  cases pairDecode w with
  | none => rfl
  | some ab =>
    obtain ⟨a, b⟩ := ab
    dsimp only
    cases F.decD i a <;> cases decodeFin (F.encD i default).length b <;> rfl

variable {F} in
/-- **The published domain of the padded collection** (ruling "published domain equivalence",
2026-11-06): `D'_i ≃ D_i × {0,1}^{|encD_i(default)|}`, the identity on the definition.
Consumers read the domain of `F.glPad m henc` through it, not by reducing the field `D`. -/
def glPad_domEquiv (m : PolyExpr)
    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n)
    (i : List Bool) :
    (F.glPad m henc).D i ≃ F.D i × (Fin (F.encD i default).length → Bool) :=
  Equiv.refl _

variable {F} in
/-- The domain equivalence of the padded collection is the identity on the definition. -/
theorem glPad_domEquiv_apply (m : PolyExpr)
    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n)
    (i : List Bool) (z : (F.glPad m henc).D i) : glPad_domEquiv m henc i z = z := rfl

variable {F} in
/-- The encoding of the padded collection through its domain equivalence `e`:
`encD'_i z = ⟨encD_i (e z).1, (e z).2⟩`. -/
theorem glPad_encD (m : PolyExpr)
    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n)
    (i : List Bool) (z : (F.glPad m henc).D i) :
    (F.glPad m henc).encD i z =
      pairEncode (F.encD i (glPad_domEquiv m henc i z).1)
        (List.ofFn (glPad_domEquiv m henc i z).2) := rfl

variable {F} in
/-- The decoder of the padded collection through its domain equivalence `e`:
`decD'_i w = e⁻¹ <$> glPadDecode F i |encD_i(default)| w`. -/
theorem glPad_decD (m : PolyExpr)
    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n)
    (i w : List Bool) :
    (F.glPad m henc).decD i w =
      (glPadDecode F i (F.encD i default).length w).map (glPad_domEquiv m henc i).symm := by
  rw [glPad_decD_eq]
  cases glPadDecode F i (F.encD i default).length w <;> rfl

variable {F} in
/-- The function of the padded collection through its domain equivalence `e`:
`g_i z = ⟨f_i (e z).1, (e z).2⟩`. -/
theorem glPad_f_domEquiv (m : PolyExpr)
    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n)
    (i : List Bool) (z : (F.glPad m henc).D i) :
    (F.glPad m henc).f i z =
      pairEncode (F.f i (glPad_domEquiv m henc i z).1)
        (List.ofFn (glPad_domEquiv m henc i z).2) := rfl

variable {F} in
/-- The sampler of the padded collection: `ofPolyTimeUniform` of `glPadSampleFun F` with
`Sample.coins + m` coins. -/
theorem glPad_sample (m : PolyExpr)
    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n) :
    (F.glPad m henc).sample =
      NUPPT.ofPolyTimeUniform (glPadSampleFun_poly F) (.add F.sample.coins m) := rfl

variable {F} in
/-- The evaluator of the padded collection: `⟨i, ⟨x, r⟩⟩ ↦ ⟨eval ⟨i, x⟩, r⟩`. -/
theorem glPad_eval (m : PolyExpr)
    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n)
    (w : List Bool) :
    (F.glPad m henc).eval w =
      pairEncode (F.eval (pairEncode (pairFstD w) (pairFstD (pairSndD w))))
        (pairSndD (pairSndD w)) := rfl

/-- **The padded collection is one-way** ([PS10, Theorem 87.3], collection form, first clause):
if `F` is a collection of one-way functions whose elements have encoding length `m(n)` at the
indices generated at parameter `n`, then `F.glPad m` is a collection of one-way functions.

**Proof sketch.** *Sampling:* with `h.sampleClose = ⟨δ, hδ, hS⟩`, at index `i = index n r`
the decoded sampler output is `(decD i (Sample(1^n, i; s₁)), decodeFin _ (ofFn s₂))` on the
coin split `splitCoins (Sample.coins n) (m n)` (`glPad_sample_runAtL`, `List.ofFn` of the
split, `uprob_comp_equiv`); `henc` gives `(encD i default).length = m n`, so the second
component decodes exactly (`decodeFin_ofFn`) and `StatClose.prod (hS n r) (StatClose.refl _)`
with `StatClose.map` to the pair gives `SampleClose δ`. *Hard:* for `A : NUPPT` against
`F.glPad m`, the inverter `B` against `F`: coins `m + A.coins` (`NUPPT.exists_split m`, the
first `m n` coins are `r`), on `⟨1^n, ⟨i, y⟩⟩` it calls `A` once on `⟨1^n, ⟨i, ⟨y, r⟩⟩⟩`
(`NUPPT.exists_comp`, `NUPPT.exists_seq`) and returns the first component of the answer
(`pairFstD`). Then `(F.glPad m).invProbAt A n ≤ F.invProbAt B n`: unfold both `uexp` over
`Gen`'s coins (`OneWay.uexp_mono`), split the inner `uprob` over `D_i × ({0,1}^{m n} × A.Coins n)`
against `D_i × B.Coins n` by `uprob_comp_equiv` on `splitCoins`, and `uprob_mono`: a decoded
answer `(x', r')` with `⟨f_i(x'), r'⟩ = ⟨f_i(x), r⟩` has `f_i(x') = f_i(x)`
(`pairEncode_injective`). `Negligible.mono` with `h.hard B`. -/
theorem OneWay.glPad {F : Collection} (m : PolyExpr)
    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n)
    (h : F.OneWay) : (F.glPad m henc).OneWay := by
  obtain ⟨δ, hδ, hS⟩ := h.sampleClose
  refine ⟨⟨δ, hδ, fun n r => ?_⟩, fun A => ?_⟩
  · have key := statClose_glPadSampler F m (F.glPad m henc).sample rfl (glPad_sample_runAtL m henc)
      hS n r _ (henc n r default)
    simp only [glPad_decD_eq] at key ⊢
    exact key
  · refine (h.hard (glPadCollInvMachine A m)).mono ⟨0, fun n _ => ?_⟩
    rw [abs_of_nonneg (invProbAt_nonneg _ _ _), abs_of_nonneg (invProbAt_nonneg _ _ _)]
    have key := glPad_invProbAt_le F m A n (fun r => (F.encD (F.index n r) default).length)
      (fun r => henc n r default)
    simp only [Collection.invProbAt_eq] at key ⊢
    simp only [glPad_decD_eq]
    exact key

/-- **`⟨x, r⟩` is hard-core for the padded collection** ([PS10, Theorem 87.3], collection form,
second clause; inventory Thm-87.3.coll, needed by Theorem 104.4): if `F` is a collection of
one-way functions with encoding length `m(n)` at generated indices, then
`h_i(x, r) = ⟨encD_i x, r⟩` is a hard-core predicate for `F.glPad m` (`Collection.HardCore`).

Repair (run-3 audit P4-2): statement unchanged. The run-2 sketch transferred the cube lemma
`HardcoreBit.invProb_guessInverter` to `D_i` by "identifying `D_i` with `{0,1}^{m n}` through
the injective encoding"; that step is invalid — the image of `encD_i` is in general a strict
subset of the cube (`Z_N^*`, `QR_N`), the uniform `x ∈ D_i` is not a uniform cube element and
the predictor's behaviour off the image is uncontrolled. The transfer is replaced by the
encoded-domain lemma `HardcoreBit.invProb_guessInverter_enc_pad`
(`Asymptotic/GoldreichLevinDomain.lean`), stated for `x` uniform on an arbitrary finite type
with an arbitrary encoding into `{0,1}^m`.

**Proof sketch.** *Easy:* `⟨i, ⟨a, b⟩⟩ ↦ ipFun ⟨padToLen a b, b⟩` — pad `a = encD_i x` to the
length of `b = r` and apply the inner-product evaluator (`exists_glBitCollEvaluator`,
`Asymptotic/HardCoreGLColl.lean`). *Hard:* `glColl_negligible` with the padding length
`L n r = |encD_i(default)| = m(n)` (`henc`) and the one-wayness of the padded collection
(`OneWay.glPad`, its inversion experiment rewritten by `glPad_decD_eq`): by contradiction,
`not_negligible_iff` gives `c` with `1/2 + n^{−c} ≤ E_r[Pr[A(1^n, ⟨i, ⟨f_i x, r⟩⟩) = ⟨encD_i x, r⟩]]`
infinitely often; the good indices (`HardcoreBit.half_le_uprob_threshold`) have per-index
success `≥ 1/2 + n^{−c}/2`, where `HardcoreBit.invProb_guessInverter_enc_pad` with
`enc := padFin (m n) ∘ encD_i` and the hard-wired `k(n) = size (8 m(n) n^{2c})` (`glKc`) makes
the recovery procedure of [PS10, Algorithm 89.6] output `encD_i x` with probability
`≥ ε/(4·2^{k(n)})`, `ε = n^{−c}/2`; the inverter `glCollMachine` (the recovery machine `glMachine`
on the pre-processed predictor `⟨⟨i, y⟩, q⟩ ↦ ⟨i, ⟨y, q⟩⟩`, output `⟨x', r⟩`) realises it
(`glColl_uprob_le`); averaging over the good indices (`HardcoreBit.uprob_mul_le_uexp`) gives
inversion probability `≥ ε²/(4·2^{k(n)})`, inverse polynomial infinitely often, contradicting
`(OneWay.glPad m henc h).hard`. -/
theorem OneWay.glPad_hardCore {F : Collection} (m : PolyExpr)
    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n)
    (h : F.OneWay) : (F.glPad m henc).HardCore F.glBit := by
  refine ⟨?_, fun A => ?_⟩
  · obtain ⟨H, hH, hHx⟩ := exists_glBitCollEvaluator F
    exact ⟨H, hH, fun i x => hHx i x.1 x.2⟩
  · have hmax : ∀ x : ℝ, x ≤ 1 / 2 + max 0 (x - 1 / 2) := fun x => by
      linarith [le_max_right (0 : ℝ) (x - 1 / 2)]
    refine ⟨_, glColl_negligible F m (fun n r => (F.encD (F.index n r) default).length)
      (fun n r => henc n r default) henc A (fun B => ?_), fun n => hmax _⟩
    have key := (OneWay.glPad m henc h).hard B
    unfold Collection.invProbAt at key
    simp only [glPad_decD_eq] at key
    exact key

end Collection

/-- **Goldreich–Levin for collections** ([PS10, Theorem 87.3], the collection form the text
uses for Theorem 104.4 and Chapter 4): for a collection `F` of one-way functions with
encoding length `m(n)` at generated indices, `g_i(x, r) = (f_i(x), r)` is a collection of
one-way functions and `⟨x, r⟩` is hard-core for it. -/
theorem goldreich_levin_coll {F : Collection} (m : PolyExpr)
    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n)
    (h : F.OneWay) : (F.glPad m henc).OneWay ∧ (F.glPad m henc).HardCore F.glBit :=
  ⟨Collection.OneWay.glPad m henc h, Collection.OneWay.glPad_hardCore m henc h⟩

/-- The padded collection of a collection of permutations is a collection of permutations
[PS10, Theorem 87.3, "(OWP)"]: `g_i = perm_i × id` on `D_i × {0,1}^{|encD_i default|}`. -/
noncomputable def PermCollection.glPad (P : PermCollection) (m : PolyExpr)
    (henc : ∀ n (r : P.gen.Coins n) (x : P.D (P.index n r)), (P.encD (P.index n r) x).length = m.eval n) :
    PermCollection :=
  { P.toCollection.glPad m henc with
    perm := fun i => (P.perm i).prodCongr (Equiv.refl _)
    f_perm := fun i z => by simp [Collection.glPad, P.f_perm] }

/-- Unfolding: the underlying collection of `P.glPad m henc` is `P.toCollection.glPad m henc`. -/
theorem PermCollection.glPad_toCollection (P : PermCollection) (m : PolyExpr)
    (henc : ∀ n (r : P.gen.Coins n) (x : P.D (P.index n r)), (P.encD (P.index n r) x).length = m.eval n) :
    (P.glPad m henc).toCollection = P.toCollection.glPad m henc := rfl

/-- **The published domain of the padded permutation collection**:
`(P.glPad m henc).D i ≃ D_i × {0,1}^{|encD_i(default)|}`, the identity on the definition. -/
def PermCollection.glPad_domEquiv (P : PermCollection) (m : PolyExpr)
    (henc : ∀ n (r : P.gen.Coins n) (x : P.D (P.index n r)), (P.encD (P.index n r) x).length = m.eval n)
    (i : List Bool) :
    (P.glPad m henc).D i ≃ P.D i × (Fin (P.encD i default).length → Bool) :=
  Equiv.refl _

/-- The domain equivalence of the padded permutation collection is the identity. -/
theorem PermCollection.glPad_domEquiv_apply (P : PermCollection) (m : PolyExpr)
    (henc : ∀ n (r : P.gen.Coins n) (x : P.D (P.index n r)), (P.encD (P.index n r) x).length = m.eval n)
    (i : List Bool) (z : (P.glPad m henc).D i) : P.glPad_domEquiv m henc i z = z := rfl

/-- The permutation of the padded permutation collection through its domain equivalence `e`:
`e⁻¹ ∘ (perm_i × id) ∘ e`. -/
theorem PermCollection.glPad_perm (P : PermCollection) (m : PolyExpr)
    (henc : ∀ n (r : P.gen.Coins n) (x : P.D (P.index n r)), (P.encD (P.index n r) x).length = m.eval n)
    (i : List Bool) :
    (P.glPad m henc).perm i = ((P.glPad_domEquiv m henc i).trans
      ((P.perm i).prodCongr (Equiv.refl _))).trans (P.glPad_domEquiv m henc i).symm :=
  rfl

/-- **The padded permutation collection is one-way** when the original is (collection form of
[PS10, Theorem 87.3] for Definition 55.1). -/
theorem PermCollection.OneWay.glPad {P : PermCollection} (m : PolyExpr)
    (henc : ∀ n (r : P.gen.Coins n) (x : P.D (P.index n r)), (P.encD (P.index n r) x).length = m.eval n)
    (h : P.OneWay) : (P.glPad m henc).OneWay :=
  Collection.OneWay.glPad m henc h

/-- **`⟨x, r⟩` is hard-core for the padded permutation collection**. -/
theorem PermCollection.OneWay.glPad_hardCore {P : PermCollection} (m : PolyExpr)
    (henc : ∀ n (r : P.gen.Coins n) (x : P.D (P.index n r)), (P.encD (P.index n r) x).length = m.eval n)
    (h : P.OneWay) : (P.glPad m henc).toCollection.HardCore P.glBit :=
  Collection.OneWay.glPad_hardCore m henc h

/-- The padded collection of a collection of trapdoor permutations is a collection of
trapdoor permutations [PS10, Theorem 87.3 for Definition 56.1, as used in Theorem 104.4]:
`Inv'(1^n, ⟨t, ⟨y, r⟩⟩) = ⟨Inv(1^n, ⟨t, y⟩), r⟩`.

**Proof sketch** (of `inv_spec`). Unfold the activation of the `ofPolyTimeUniform` machine
(`NUPPT.output_ofPolyTime`, the layout projections); `T.inv` is uniform so its activation is
its output on the layout with empty advice; `T.inv_spec` decodes the first component to
`(perm i).symm y.1` and `decodeFin_ofFn` the second to `y.2`. -/
noncomputable def TrapdoorCollection.glPad (T : TrapdoorCollection) (m : PolyExpr)
    (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n) :
    TrapdoorCollection :=
  { T.toPermCollection.glPad m henc with
    inv := NUPPT.ofPolyTimeUniform (glPadInvFun_poly T) T.inv.coins
    inv_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
    inv_spec := fun n r y s => by
      have hspec := T.inv_spec n r y.1 (NUPPT.coinsCongr (NUPPT.coins_ofPolyTimeUniform _ _) n s)
      rw [NUPPT.runAt_eq T.inv, NUPPT.coinsCongr_ofFn, T.inv_uniform.runAtL_eq] at hspec
      rw [NUPPT.runAt_eq (NUPPT.ofPolyTimeUniform (glPadInvFun_poly T) T.inv.coins),
        NUPPT.runAtL_ofPolyTimeUniform]
      simp only [glPadInvFun_eq, NUPPT.inParam_eq, NUPPT.inArg_eq, NUPPT.inCoins_eq,
        NUPPT.advInput_eq, NUPPT.layout_eq, pairFstD_pairEncode, pairSndD_pairEncode,
        PermCollection.glPad, Collection.glPad, pairDecode_pairEncode, decodeFin_ofFn,
        NUPPT.coinLen_eq, NUPPT.coins_ofPolyTimeUniform] at hspec ⊢
      rw [hspec]
      rfl }

/-- Unfolding: the underlying permutation collection of `T.glPad m henc` is
`T.toPermCollection.glPad m henc`. -/
theorem TrapdoorCollection.glPad_toPermCollection (T : TrapdoorCollection) (m : PolyExpr)
    (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n) :
    (T.glPad m henc).toPermCollection = T.toPermCollection.glPad m henc := rfl

/-- **The published domain of the padded trapdoor collection**:
`(T.glPad m henc).D i ≃ D_i × {0,1}^{|encD_i(default)|}`, the identity on the definition. -/
def TrapdoorCollection.glPad_domEquiv (T : TrapdoorCollection) (m : PolyExpr)
    (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n)
    (i : List Bool) :
    (T.glPad m henc).D i ≃ T.D i × (Fin (T.encD i default).length → Bool) :=
  Equiv.refl _

/-- The domain equivalence of the padded trapdoor collection is the identity. -/
theorem TrapdoorCollection.glPad_domEquiv_apply (T : TrapdoorCollection) (m : PolyExpr)
    (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n)
    (i : List Bool) (z : (T.glPad m henc).D i) : T.glPad_domEquiv m henc i z = z := rfl

/-- The trapdoor inverter of the padded trapdoor collection: `ofPolyTimeUniform` of
`glPadInvFun T` with the coins of `T.inv`. -/
theorem TrapdoorCollection.glPad_inv (T : TrapdoorCollection) (m : PolyExpr)
    (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n) :
    (T.glPad m henc).inv = NUPPT.ofPolyTimeUniform (glPadInvFun_poly T) T.inv.coins := rfl

/-- **The padded trapdoor collection is one-way** when the original is ([PS10, Theorem 87.3]
for Definition 56.1 (5)). -/
theorem TrapdoorCollection.OneWay.glPad {T : TrapdoorCollection} (m : PolyExpr)
    (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n)
    (h : T.OneWay) : (T.glPad m henc).OneWay :=
  Collection.OneWay.glPad m henc h

/-- **`⟨x, r⟩` is hard-core for the padded trapdoor collection**: the hypothesis "trapdoor
permutations with a hard-core predicate" of [PS10, Theorem 104.4] is satisfiable from trapdoor
permutations whose generated indices encode elements in exactly `m(n)` bits (`henc`; no
candidate of the library satisfies it as parametrized, see `Collection.glPad`). -/
theorem TrapdoorCollection.OneWay.glPad_hardCore {T : TrapdoorCollection} (m : PolyExpr)
    (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n)
    (h : T.OneWay) : (T.glPad m henc).toCollection.HardCore T.glBit :=
  Collection.OneWay.glPad_hardCore m henc h

/-- **`⟨x, r⟩` is hard-core for the padded trapdoor collection**, the predicate read through the
published domain equivalence `e = T.glPad_domEquiv m henc`: `z ↦ ⟨(e z).1, (e z).2⟩` is
hard-core for `T.glPad m henc` (the form of `glPad_hardCore` that a consumer states without
reducing the domain of `T.glPad`; `e` is the identity). -/
theorem TrapdoorCollection.OneWay.glPad_hardCore_domEquiv {T : TrapdoorCollection} (m : PolyExpr)
    (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n)
    (h : T.OneWay) :
    (T.glPad m henc).toCollection.HardCore fun i z => T.glBit i (T.glPad_domEquiv m henc i z) :=
  h.glPad_hardCore m henc

end TCSlib.Cryptography


/- ===== gate 07 statement sweep: seal-candidate collector (appended to the statement-only copy) =====
Walks every constant declared in this file (the current module of the statement-only copy, in which
every theorem/lemma/example value is `sorry`): the TYPE of every constant (theorems, definitions,
instances, structures and their fields/constructors/recursors, auxiliaries), and the VALUE of every
definition/instance/abbreviation/opaque (theorem values are `sorry`, so proofs contribute nothing).
Every TCSlib constant declared in another module that occurs there is classified:
* `def` (a plain, non-instance, non-reducible, non-projection, non-auxiliary, non-private
  definition): a seal candidate. Its value and its type are walked further (`deep` tier).
* instance / `@[reducible]` (incl. `abbrev`) / private / auxiliary (matcher, `_unary`, …):
  transparent or unnameable, so not sealed; recorded, and their values and types are walked.
* any other constant (theorem, structure, inductive, constructor, projection, axiom, …): its TYPE is
  walked (using a constant can make the elaborator reduce its type), it is not sealed.
`direct` = occurs in this file's types/values; `deep` = reached only through a foreign constant.
Output: SWEEP_OUT.cands.tsv, SWEEP_OUT.uses.tsv, SWEEP_OUT.transparent.tsv -/
namespace SweepCollect
open Lean
def numSuffix (s pre : String) : Bool :=
  s.startsWith pre && (s.drop pre.length).length > 0 && (s.drop pre.length).all Char.isDigit
def isAuxComp (s : String) : Bool :=
  s.startsWith "_" || numSuffix s "match_" || numSuffix s "proof_" || numSuffix s "eq_" ||
    s == "eq_def" || s == "eq_unfold"
def isAuxName : Name → Bool
  | .str p s => isAuxComp s || isAuxName p
  | .num _ _ => true
  | .anonymous => false
end SweepCollect

open Lean Meta in
run_cmd do
  let env ← getEnv
  let outBase : String := "/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/e1/final6c/control/work/TCSlib_Cryptography_Asymptotic_HardCoreCollection.coll"
  let modNames := env.header.moduleNames
  let isTCS (j : ModuleIdx) : Bool := (modNames[j.toNat]!).getRoot == `TCSlib
  let kindOf (n : Name) : String :=
    match env.find? n with
    | some (.defnInfo _) =>
      if isPrivateName n then "private"
      else if SweepCollect.isAuxName n || isMatcherCore env n || isAuxRecursor env n || isNoConfusion env n then "aux"
      else if env.isProjectionFn n then "proj"
      else if isInstanceCore env n then "instance"
      else if getReducibilityStatusCore env n == .reducible then "reducible"
      else if getReducibilityStatusCore env n == .irreducible then "irreducible"
      else "def"
    | some (.thmInfo _) => "thm"
    | some (.axiomInfo _) => "axiom"
    | some (.opaqueInfo _) => "opaque"
    | some (.inductInfo _) => "inductive"
    | some (.ctorInfo _) => "ctor"
    | some (.recInfo _) => "rec"
    | some (.quotInfo _) => "quot"
    | none => "none"
  -- local constants of this file
  let locals := env.constants.map₂.toList.filter fun (n, _) => !(n.components.contains `SweepCollect)
  -- candidate ↦ (tier, via set, owners)
  let mut cands : Std.HashMap Name (String × NameSet × NameSet) := {}
  let mut transp : Std.HashMap Name (String × NameSet) := {}
  let mut uses : Array String := #[]
  for (ln, ci) in locals do
    -- owner: strip auxiliary components / private prefix
    let owner := (privateToUserName? ln).getD ln
    let roots : Array (Name × String) :=
      (ci.type.getUsedConstantsAsSet.toArray.map (·, "T")) ++
      (match ci with
       | .defnInfo dv => dv.value.getUsedConstantsAsSet.toArray.map (·, "V")
       | .opaqueInfo ov => ov.value.getUsedConstantsAsSet.toArray.map (·, "V")
       | .thmInfo tv => tv.value.getUsedConstantsAsSet.toArray.map (·, "V")
       | _ => #[])
    -- worklist: (constant, region T/V, via (anonymous = direct))
    let mut work : Array (Name × String × Name) := roots.map fun (n, r) => (n, r, Name.anonymous)
    let mut seen : Std.HashSet (Name × String) := {}
    let mut found : Array String := #[]
    while !work.isEmpty do
      let (u, r, via) := work.back!
      work := work.pop
      if seen.contains (u, r) then continue
      seen := seen.insert (u, r)
      let some j := env.getModuleIdxFor? u | continue   -- local or unknown: locals are walked as roots
      unless isTCS j do continue
      let some cu := env.find? u | continue
      let k := kindOf u
      let via' := if via.isAnonymous then u else via
      if k == "def" then
        let tier := if via.isAnonymous then "direct" else "deep"
        let (t0, vs, os) := cands.getD u (tier, {}, {})
        let t1 := if t0 == "direct" || tier == "direct" then "direct" else "deep"
        cands := cands.insert u (t1, if via.isAnonymous then vs else vs.insert via, os.insert owner)
        if via.isAnonymous then found := found.push s!"{u}@{r}"
      else if k == "instance" || k == "reducible" || k == "private" || k == "aux" || k == "proj" then
        let (m0, os) := transp.getD u (k, {})
        transp := transp.insert u (m0, os.insert owner)
      -- walk further: the type always; the value of definitions (sealed or transparent)
      for v in cu.type.getUsedConstantsAsSet.toArray do
        unless seen.contains (v, r) do work := work.push (v, r, via')
      if let .defnInfo dv := cu then
        for v in dv.value.getUsedConstantsAsSet.toArray do
          unless seen.contains (v, r) do work := work.push (v, r, via')
    if !found.isEmpty then
      uses := uses.push s!"{owner}\t{ln}\t{" ".intercalate found.toList}"
  let mut cl : Array String := #[]
  for (n, (t, vs, os)) in cands.toArray.qsort (fun a b => Name.lt a.1 b.1) do
    let some j := env.getModuleIdxFor? n | continue
    let vsT := ", ".intercalate ((vs.toArray.qsort Name.lt).toList.take 3 |>.map toString)
    cl := cl.push s!"{n}\t{modNames[j.toNat]!}\t{t}\t{vsT}\t{os.size}"
  IO.FS.writeFile (outBase ++ ".cands.tsv") ("\n".intercalate cl.toList ++ "\n")
  IO.FS.writeFile (outBase ++ ".uses.tsv") ("\n".intercalate uses.toList ++ "\n")
  let mut tl : Array String := #[]
  for (n, (k, os)) in transp.toArray.qsort (fun a b => Name.lt a.1 b.1) do
    let some j := env.getModuleIdxFor? n | continue
    tl := tl.push s!"{n}\t{k}\t{modNames[j.toNat]!}\t{os.size}"
  IO.FS.writeFile (outBase ++ ".transparent.tsv") ("\n".intercalate tl.toList ++ "\n")
  -- own-file dependency graph (for the minimiser's cascade/masking rule): for every local constant,
  -- its declaration line and the declaration lines of the local constants its type/value mentions
  let lineOf (n : Name) : Lean.Elab.Command.CommandElabM Int := do
    let mut cur := n
    for _ in [0:8] do
      if let some r ← Lean.findDeclarationRanges? cur then return (r.range.pos.line : Int)
      if let some u := privateToUserName? cur then
        if let some r ← Lean.findDeclarationRanges? u then return (r.range.pos.line : Int)
      match cur with
      | .str p _ => cur := p
      | .num p _ => cur := p
      | .anonymous => return -1
    return -1
  let localSet : NameSet := locals.foldl (fun s (n, _) => s.insert n) {}
  let mut dl : Array String := #[]
  for (ln, ci) in locals do
    -- theorem values included: top-level theorem values are `sorry` here, but the auxiliary
    -- theorems `D.proof_N` abstracted from a definition's body carry that body's proofs
    let refs := ci.type.getUsedConstantsAsSet.toArray ++
      (match ci with
       | .defnInfo dv => dv.value.getUsedConstantsAsSet.toArray
       | .opaqueInfo ov => ov.value.getUsedConstantsAsSet.toArray
       | .thmInfo tv => tv.value.getUsedConstantsAsSet.toArray
       | _ => #[])
    let mut ls : Array Int := #[]
    for v in refs do
      if localSet.contains v && v != ln then
        let l ← lineOf v
        unless ls.contains l do ls := ls.push l
    let l0 ← lineOf ln
    dl := dl.push s!"{l0}\t{ln}\t{" ".intercalate (ls.toList.map toString)}"
  IO.FS.writeFile (outBase ++ ".deps.tsv") ("\n".intercalate dl.toList ++ "\n")
