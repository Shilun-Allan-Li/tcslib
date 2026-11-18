/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.Regev.Experiments
import TCSlib.Cryptography.LWE.Assumption
import TCSlib.Cryptography.Asymptotic.Realization
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
import TCSlib.Cryptography.Encoding.ModularArithmetic
import Mathlib.Data.Fin.Tuple.Take

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Regev public-key encryption: asymptotic single-bit security

## Main definitions

* `encodeView`: a public key and one ciphertext as a bit string: the key through
  `LWE.encodeChallenge`, then the vector component through `Encoding.Modular.encodeVector`,
  then the residue numeral.
* `encryptAdvice`, `encryptPre`: the reduction's advice at one parameter and its
  polynomial-time pre-processing, which encrypts the fixed bit under an encoded challenge key
  with subset coins read from the input.
* `encryptAdviceBound`: a syntactic polynomial bounding the advice length.

## Main results

* `encryptPre_encryptAdvice`, `polyTimeComputable_encryptPre`: the pre-processing computes the
  encoded view `encodeView (view μ pk r)` and is polynomial-time.
* `exists_reductionMachine`: for every `NUPPT` view distinguisher `D` and bit `μ` there is an
  `NUPPT` `D'` whose DLWE advantage is exactly that of the function-level `reduction` on `D`.
* `singleBitSecure_of_dlweAssumption`: under `DLWEAssumption F` and the width condition, every
  `NUPPT` distinguisher of the encoded real views of `0` and `1` has negligible advantage.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, 17 February 2016, Section 5.2.1
  (Regev's cryptosystem and its hybrids) and Definition 4.2.3 (decisional LWE).
* [Wu24] D. Wu, CS395T *Topics in Cryptography*, Spring 2024 notes, Lecture 21.
* [Vad12] S. Vadhan, *Pseudorandomness*, 2012, Theorem 6.18 (through `extractionError` only).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd ed., January 2010,
  Definition 26.8 (non-uniform PPT machines).

**The reduction machine.** The function-level `reduction` draws `m` subset coins `r`, forms
the ciphertext `(Aᵀ r, ⟨b, r⟩ + codepoint μ)` under the challenge key `(A, b)`, and runs the
view distinguisher on the key and the ciphertext. Its machine draws the subset coins as its
own: `NUPPT.exists_split` hands the first `S(κ)` coins (`S` the family's sample polynomial,
`m ≤ S`) to the input; the first `m` of them are the subset, the rest are unread. The
pre-processing (`encryptPre`) computes the ciphertext with the public toolkit
`Encoding.ModularArithmetic` (`subsetSumModWords`, `addMod`); the parameters `n`, `m`, `q`, the
width and the codepoint of `μ` are advice. The realiser is built with
`NUPPT.exists_realizesOn_of_preTarget_id`. This is the content that the GSW analogue on PR #377
(`GSW/Asymptotic.lean`, `ReductionEfficient`) takes as a hypothesis, here proved for Regev;
nothing is shared with that file. The statements are over the raw `LWE.Family` and make no
claim about the honest algorithms' efficiency.
-/

namespace TCSlib.Cryptography.Encryption.PublicKey.Regev

open Complexity Turing
open LWE (Parameters Noise)
open Encoding.ModularArithmetic

/-! ## The encoded view -/

/-- **The encoded view** of a public key and one ciphertext at width `w`: the key through
`LWE.encodeChallenge P w`, followed by `encodeVector w` of the ciphertext's vector and the
`w`-bit numeral of its residue. Glue: the binary representation of the passive view of
[Pei16, §5.2.1] ([PS10, §2.1]). -/
def encodeView (P : Parameters) (w : ℕ)
    (v : (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) ×
      ((Fin P.dimension → ZMod P.modulus) × ZMod P.modulus)) : List Bool :=
  LWE.encodeChallenge P w v.1 ++
    (Encoding.Modular.encodeVector w v.2.1 ++ Candidates.natToList w v.2.2.val)

/-- `encodeView P w (pk, (u, c)) = encodeChallenge P w pk ++ (encodeVector w u ++
natToList w c.val)`. -/
theorem encodeView_eq (P : Parameters) (w : ℕ)
    (v : (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) ×
      ((Fin P.dimension → ZMod P.modulus) × ZMod P.modulus)) :
    encodeView P w v = LWE.encodeChallenge P w v.1 ++
      (Encoding.Modular.encodeVector w v.2.1 ++ Candidates.natToList w v.2.2.val) := rfl

/-- An encoded view has `m (n + 1) w + n w + w` bits.

**Proof sketch.** `LWE.encodeChallenge_length`, `encodeVector_length` and
`Candidates.length_natToList`. -/
theorem encodeView_length (P : Parameters) (w : ℕ)
    (v : (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) ×
      ((Fin P.dimension → ZMod P.modulus) × ZMod P.modulus)) :
    (encodeView P w v).length = P.samples * (P.dimension + 1) * w + (P.dimension * w + w) := by
  rw [encodeView_eq, List.length_append, List.length_append, LWE.encodeChallenge_length,
    Encoding.Modular.encodeVector_length, Candidates.length_natToList]

/-! ## The pre-processing and its advice -/

/-- **The encryption reduction's advice** at parameters `P`, width `w` and bit `μ`:
`⟨⟨modContext w q, ⟨1^n, 1^m⟩⟩, ⟨1^{m n w}, natToList w (codepoint μ).val⟩⟩`. Glue: the
non-uniform advice of the reduction of [Pei16, §5.2.1] ([PS10, Definition 26.8]). -/
def encryptAdvice (P : Parameters) (w : ℕ) (μ : Bool) : List Bool :=
  pairEncode (pairEncode (modContext w P.modulus)
      (pairEncode (List.replicate P.dimension true) (List.replicate P.samples true)))
    (pairEncode (List.replicate (P.samples * P.dimension * w) true)
      (Candidates.natToList w (LWE.BitEncoding.codepoint P μ).val))

/-- `encryptAdvice P w μ = ⟨⟨modContext w q, ⟨1^n, 1^m⟩⟩, ⟨1^{m n w},
natToList w (codepoint μ).val⟩⟩`. -/
theorem encryptAdvice_eq (P : Parameters) (w : ℕ) (μ : Bool) :
    encryptAdvice P w μ =
      pairEncode (pairEncode (modContext w P.modulus)
          (pairEncode (List.replicate P.dimension true) (List.replicate P.samples true)))
        (pairEncode (List.replicate (P.samples * P.dimension * w) true)
          (Candidates.natToList w (LWE.BitEncoding.codepoint P μ).val)) := rfl

/-- The advice has `2 m n w + 4 n + 2 m + 13 w + 24` bits.

**Proof sketch.** `length_pairEncode`, `modContext_length`, `List.length_replicate` and
`Candidates.length_natToList`. -/
theorem encryptAdvice_length (P : Parameters) (w : ℕ) (μ : Bool) :
    (encryptAdvice P w μ).length =
      2 * (P.samples * P.dimension * w) + 4 * P.dimension + 2 * P.samples + 13 * w + 24 := by
  rw [encryptAdvice_eq, length_pairEncode, length_pairEncode, length_pairEncode,
    length_pairEncode, modContext_length, List.length_replicate, List.length_replicate,
    List.length_replicate, Candidates.length_natToList]
  ring

/-- **The encryption pre-processing.** On `⟨adv, ⟨y, s⟩⟩` with
`adv = ⟨⟨ctx, ⟨nT, mT⟩⟩, ⟨cut, cp⟩⟩`, an encoded challenge key `y` and subset bits `s`: split
`y` after `|cut|` bits into the matrix rows and the value block, and output `y` followed by
the subset sum of the rows (`subsetSumModWords ctx nT mT`) and the numeral of the value
block's subset sum plus `cp` modulo `q` (`subsetSumModWords ctx [true] mT`, `addMod`). Glue:
the deterministic part of the reduction of [Pei16, §5.2.1]. -/
def encryptPre (z : List Bool) : List Bool :=
  let adv := pairFstD z
  let y := pairFstD (pairSndD z)
  let s := pairSndD (pairSndD z)
  let ctx := pairFstD (pairFstD adv)
  let nT := pairFstD (pairSndD (pairFstD adv))
  let mT := pairSndD (pairSndD (pairFstD adv))
  let cut := (pairFstD (pairSndD adv)).length
  y ++ (subsetSumModWords ctx nT mT (y.take cut) s ++
    addMod (pairEncode ctx (pairEncode (subsetSumModWords ctx [true] mT (y.drop cut) s)
      (pairSndD (pairSndD adv)))))

/-- `encryptPre ⟨adv, ⟨y, s⟩⟩` is `y` followed by the encoded subset sum of the first `|cut|`
bits of `y` and the numeral of the remaining block's subset sum plus `cp`, through the total
projections. -/
theorem encryptPre_eq (z : List Bool) :
    encryptPre z =
      let adv := pairFstD z
      let y := pairFstD (pairSndD z)
      let s := pairSndD (pairSndD z)
      let ctx := pairFstD (pairFstD adv)
      let nT := pairFstD (pairSndD (pairFstD adv))
      let mT := pairSndD (pairSndD (pairFstD adv))
      let cut := (pairFstD (pairSndD adv)).length
      y ++ (subsetSumModWords ctx nT mT (y.take cut) s ++
        addMod (pairEncode ctx (pairEncode (subsetSumModWords ctx [true] mT (y.drop cut) s)
          (pairSndD (pairSndD adv))))) := rfl

/-- **The pre-processing computes the encoded view** [Pei16, §5.2.1, representation]: if
`q ≤ 2^w`, then on the advice of `μ`, the encoded key `pk` and subset bits `ofFn r ++ extra`,
`encryptPre` returns `encodeView P w (view P μ pk r)`.

**Proof sketch.** The encoded key is `encodeMatrix w A ++ encodeVector w b`
(`LWE.encodeChallenge_eq`), cut after `|encodeMatrix w A| = m n w` bits. By
`subsetSumModWords_modContext` the rows give `encodeVector w (Aᵀ *ᵥ r)`, the ciphertext's
vector (`encrypt_fst`); by `subsetSumModWords_modContext_vector` and `addMod_modContext` the
value block gives the numeral of `∑ i, b i r i + codepoint μ`, its residue (`encrypt_snd`). -/
theorem encryptPre_encryptAdvice (P : Parameters) (w : ℕ) (hq : P.modulus ≤ 2 ^ w) (μ : Bool)
    (pk : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) (r : Fin P.samples → Bool) (extra : List Bool) :
    encryptPre (pairEncode (encryptAdvice P w μ)
        (pairEncode (LWE.encodeChallenge P w pk) (List.ofFn r ++ extra))) =
      encodeView P w (view P μ pk r) := by
  have hcut : (Encoding.Modular.encodeMatrix w pk.1).length =
      (List.replicate (P.samples * P.dimension * w) true).length := by
    rw [Encoding.Modular.encodeMatrix_length, List.length_replicate]
  rw [encodeView_eq, view_fst, view_snd, encrypt_fst, encrypt_snd, encryptPre_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, encryptAdvice_eq]
  rw [LWE.encodeChallenge_eq, List.take_left' hcut, List.drop_left' hcut,
    subsetSumModWords_modContext hq _ _ (List.length_replicate (n := P.dimension) (a := true))
      (List.length_replicate (n := P.samples) (a := true)) pk.1 r extra,
    subsetSumModWords_modContext_vector hq _ (List.length_replicate (n := P.samples) (a := true))
      pk.2 r extra,
    addMod_modContext hq]

/-- **The encryption pre-processing is polynomial-time** on every input.

**Proof sketch.** Cut the key with `polyTimeComputable_pairTakePoly .var` and
`pairDropPoly .var` on `⟨cut, y⟩`; apply `polyTimeComputable_subsetSumModWords` to the packed
arguments (with the constant counter `[true]` for the value block),
`polyTimeComputable_addMod`, pairing and append. -/
theorem polyTimeComputable_encryptPre : PolyTimeComputable encryptPre := by
  have hadv := polyTimeComputable_pairFstD
  have hy := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hs := polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hctx := polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp hadv)
  have hnT := polyTimeComputable_pairFstD.comp
    (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp hadv))
  have hmT := polyTimeComputable_pairSndD.comp
    (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp hadv))
  have hcut := polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp hadv)
  have hcp := polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp hadv)
  have htake : PolyTimeComputable (fun z => (pairFstD (pairSndD z)).take
      (pairFstD (pairSndD (pairFstD z))).length) := by
    refine Eq.mp (congrArg PolyTimeComputable ?_)
      ((polyTimeComputable_pairTakePoly .var).comp (hcut.pairEncode hy))
    funext z
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var]
  have hdrop : PolyTimeComputable (fun z => (pairFstD (pairSndD z)).drop
      (pairFstD (pairSndD (pairFstD z))).length) := by
    refine Eq.mp (congrArg PolyTimeComputable ?_)
      ((polyTimeComputable_pairDropPoly .var).comp (hcut.pairEncode hy))
    funext z
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var]
  have hrows : PolyTimeComputable (fun z => subsetSumModWords (pairFstD (pairFstD (pairFstD z)))
      (pairFstD (pairSndD (pairFstD (pairFstD z)))) (pairSndD (pairSndD (pairFstD (pairFstD z))))
      ((pairFstD (pairSndD z)).take (pairFstD (pairSndD (pairFstD z))).length)
      (pairSndD (pairSndD z))) := by
    refine Eq.mp (congrArg PolyTimeComputable ?_) (polyTimeComputable_subsetSumModWords.comp
      (hctx.pairEncode (hnT.pairEncode (hmT.pairEncode (htake.pairEncode hs)))))
    funext z
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hvalue : PolyTimeComputable (fun z => subsetSumModWords (pairFstD (pairFstD (pairFstD z)))
      [true] (pairSndD (pairSndD (pairFstD (pairFstD z))))
      ((pairFstD (pairSndD z)).drop (pairFstD (pairSndD (pairFstD z))).length)
      (pairSndD (pairSndD z))) := by
    refine Eq.mp (congrArg PolyTimeComputable ?_) (polyTimeComputable_subsetSumModWords.comp
      (hctx.pairEncode ((polyTimeComputable_const [true]).pairEncode
        (hmT.pairEncode (hdrop.pairEncode hs)))))
    funext z
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hres := polyTimeComputable_addMod.comp (hctx.pairEncode (hvalue.pairEncode hcp))
  have hfinal := hy.append (hrows.append hres)
  refine Eq.mp (congrArg PolyTimeComputable ?_) hfinal
  funext z
  rw [encryptPre_eq]
  dsimp only [Function.comp_apply]

/-- **The advice bound** `2 S D R + 4 D + 2 S + 13 R + 24` of a family `F`, with `S`, `D`, `R`
its sample, dimension and width polynomials. Glue. -/
def encryptAdviceBound (F : LWE.Family) : PolyExpr :=
  .add (.add (.add (.add (.mul (.const 2) (.mul (.mul F.samplesBound F.dimensionBound)
    F.residueBits)) (.mul (.const 4) F.dimensionBound)) (.mul (.const 2) F.samplesBound))
    (.mul (.const 13) F.residueBits)) (.const 24)

/-- `encryptAdviceBound F` evaluates to `2 S D R + 4 D + 2 S + 13 R + 24`.

**Proof sketch.** The `PolyExpr` evaluation equations. -/
theorem encryptAdviceBound_eval (F : LWE.Family) (κ : ℕ) :
    (encryptAdviceBound F).eval κ =
      2 * (F.samplesBound.eval κ * F.dimensionBound.eval κ * F.residueBits.eval κ) +
        4 * F.dimensionBound.eval κ + 2 * F.samplesBound.eval κ +
        13 * F.residueBits.eval κ + 24 := by
  simp only [encryptAdviceBound, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]

/-- The advice of either bit at parameter `κ` has at most `(encryptAdviceBound F).eval κ` bits.

**Proof sketch.** `encryptAdvice_length`, then the family's bounds `samples_le` and
`dimension_le`, monotonically in every summand. -/
theorem encryptAdvice_length_le (F : LWE.Family) (κ : ℕ) (μ : Bool) :
    (encryptAdvice (F.parameters κ) (F.residueBits.eval κ) μ).length ≤
      (encryptAdviceBound F).eval κ := by
  rw [encryptAdvice_length, encryptAdviceBound_eval]
  have hm := F.samples_le κ
  have hn := F.dimension_le κ
  gcongr

/-! ## The reduction machine -/

/-- **The encryption reduction as a proved `NUPPT`** [Pei16, §5.2.1; PS10, Definition 26.8]:
for every family `F`, bit `μ` and `NUPPT` distinguisher `D` of the encoded views, some `NUPPT`
`D'` has, at every parameter `κ`, exactly the DLWE advantage of the function-level reduction
`reduction P μ (fun v r => D(1^κ, encodeView v; r))`:
`decisionAdvantage (reduction …) = F.advantageAt D' κ`. `D'` draws the subset coins itself;
its advice holds `n`, `m`, `q`, the width and the codepoint of `μ`.

**Proof sketch.**
1. `NUPPT.exists_realizesOn_of_preTarget_id` with `encryptPre` (`polyTimeComputable_encryptPre`),
   the advice `encryptAdvice` (bounded by `encryptAdviceBound F`) and the target
   `encryptPre_encryptAdvice`, on the challenges `⟨encodeChallenge pk, s⟩` with
   `s ∈ {0,1}^{S(κ)}`, gives `B` with `D.coins` that runs `D` on `encodeView (view μ pk r)`,
   `r` the first `m` bits of `s` (`Fin.take`, `Fin.ofFn_take_eq_take_ofFn`).
2. `NUPPT.exists_split B S` gives `D'` with coins `S + D.coins`, which hands its first `S(κ)`
   coins to `B` as the subset string.
3. Coins: the relabelling `((t, v), u) ↦ t ++ u ++ v` (`Fin.appendEquiv`, `finCongr`) of
   `({0,1}^m × D's coins) × {0,1}^{S - m}` onto `D'`'s coins makes `D'`'s verdict the
   reduction's on `(t, v)` (`hverdict`); `acceptProb_coins_equiv` and `acceptProb_coins_fst`
   (the unread `u`) turn both acceptance probabilities of the DLWE experiment into the
   reduction's. -/
theorem exists_reductionMachine (F : LWE.Family) (μ : Bool) (D : NUPPT) :
    ∃ D' : NUPPT, ∀ κ, LWE.decisionAdvantage (F.parameters κ) (F.noise κ)
      (reduction (F.parameters κ) μ
        (fun v r => D.distinguisherL κ (encodeView (F.parameters κ) (F.residueBits.eval κ) v) r))
      = F.advantageAt D' κ := by
  -- Step 1: the realiser on challenges paired with `S(κ)` subset bits.
  obtain ⟨B, hB⟩ := NUPPT.exists_realizesOn_of_preTarget_id D
    (X := fun κ => (Matrix (Fin (F.parameters κ).samples) (Fin (F.parameters κ).dimension)
      (ZMod (F.parameters κ).modulus) ×
        (Fin (F.parameters κ).samples → ZMod (F.parameters κ).modulus)) ×
      (Fin (F.samplesBound.eval κ) → Bool))
    (Ω := fun _ => Unit)
    (fun κ x => pairEncode (LWE.encodeChallenge (F.parameters κ) (F.residueBits.eval κ) x.1)
      (List.ofFn x.2))
    (fun κ _ => encryptAdvice (F.parameters κ) (F.residueBits.eval κ) μ)
    (fun κ _ x => encodeView (F.parameters κ) (F.residueBits.eval κ)
      (view (F.parameters κ) μ x.1 (Fin.take _ (F.samples_le κ) x.2)))
    polyTimeComputable_encryptPre
    (fun κ _ x => by
      dsimp only
      rw [← List.take_append_drop (F.parameters κ).samples (List.ofFn x.2),
        ← Fin.ofFn_take_eq_take_ofFn (F.samples_le κ)]
      exact encryptPre_encryptAdvice _ _ (F.modulus_le_pow κ) μ x.1 _ _)
    (fun _ => ()) (encryptAdviceBound F) (fun κ => encryptAdvice_length_le F κ μ)
  -- Step 2: the subset bits become the first `S(κ)` coins.
  obtain ⟨B₂, hc₂, -, hrun₂⟩ := NUPPT.exists_split B F.samplesBound
  refine ⟨B₂, fun κ => ?_⟩
  -- Step 3: relabel the coins.
  have hmS := F.samples_le κ
  have hcB : B.coins = D.coins := hB.coins_eq
  have hlen : (F.parameters κ).samples + (F.samplesBound.eval κ - (F.parameters κ).samples) +
      D.coinLen κ = B₂.coinLen κ := by
    rw [NUPPT.coinLen_eq, NUPPT.coinLen_eq, hc₂, PolyExpr.eval_add, hcB]
    omega
  let T := Fin (F.parameters κ).samples → Bool
  let U := Fin (F.samplesBound.eval κ - (F.parameters κ).samples) → Bool
  let φ : (T × D.Coins κ) × U ≃ B₂.Coins κ :=
    ((((Equiv.prodAssoc T (D.Coins κ) U).trans
      ((Equiv.refl T).prodCongr (Equiv.prodComm (D.Coins κ) U))).trans
        (Equiv.prodAssoc T U (D.Coins κ)).symm).trans
      ((Fin.appendEquiv _ _).prodCongr (Equiv.refl (D.Coins κ)))).trans
      ((Fin.appendEquiv _ _).trans (Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)))
  have hφ (t : T) (v : D.Coins κ) (u : U) :
      List.ofFn (φ ((t, v), u)) = List.ofFn t ++ List.ofFn u ++ List.ofFn v := by
    change List.ofFn (fun i => Fin.append (Fin.append t u) v (Fin.cast hlen.symm i)) = _
    rw [← List.ofFn_congr hlen, List.ofFn_fin_append, List.ofFn_fin_append]
  let Dv := fun (v : (Matrix (Fin (F.parameters κ).samples) (Fin (F.parameters κ).dimension)
      (ZMod (F.parameters κ).modulus) ×
        (Fin (F.parameters κ).samples → ZMod (F.parameters κ).modulus)) ×
      ((Fin (F.parameters κ).dimension → ZMod (F.parameters κ).modulus) ×
        ZMod (F.parameters κ).modulus)) (r : D.Coins κ) =>
    D.distinguisherL κ (encodeView (F.parameters κ) (F.residueBits.eval κ) v) r
  have hverdict (x : Matrix (Fin (F.parameters κ).samples) (Fin (F.parameters κ).dimension)
      (ZMod (F.parameters κ).modulus) ×
        (Fin (F.parameters κ).samples → ZMod (F.parameters κ).modulus))
      (c : (T × D.Coins κ) × U) :
      B₂.distinguisherL κ (LWE.encodeChallenge (F.parameters κ) (F.residueBits.eval κ) x) (φ c) =
        reduction (F.parameters κ) μ Dv x c.1 := by
    obtain ⟨⟨t, v⟩, u⟩ := c
    have hTU : (List.ofFn t ++ List.ofFn u).length = F.samplesBound.eval κ := by
      rw [List.length_append, List.length_ofFn, List.length_ofFn]
      omega
    obtain ⟨s, hs⟩ := exists_ofFn_eq_of_length hTU
    have ht : Fin.take _ hmS s = t := by
      apply List.ofFn_injective
      rw [Fin.ofFn_take_eq_take_ofFn, hs, List.take_left' (List.length_ofFn (f := t))]
    have hrun : B.runAtL κ (pairEncode (LWE.encodeChallenge (F.parameters κ)
        (F.residueBits.eval κ) x) (List.ofFn s)) (List.ofFn v) =
        D.runAtL κ (encodeView (F.parameters κ) (F.residueBits.eval κ)
          (view (F.parameters κ) μ x (Fin.take _ hmS s))) ((List.ofFn v).take (D.coinLen κ)) :=
      hB.runAtL_eq κ (x, s) (by rw [List.length_ofFn, NUPPT.coinLen_eq])
    rw [NUPPT.distinguisherL_eq, NUPPT.runAt_eq, hφ, hrun₂, List.take_left' hTU,
      List.drop_left' hTU, ← hs, hrun, ht, List.take_of_length_le (le_of_eq List.length_ofFn),
      reduction_eq]
    dsimp only [Dv]
    rw [NUPPT.distinguisherL_eq, NUPPT.runAt_eq]
  rw [LWE.Family.advantageAt_eq, LWE.decisionAdvantage_eq, LWE.decisionAdvantage_eq,
    distAdv_def, distAdv_def,
    ← EnsembleLemmas.acceptProb_coins_equiv φ (LWE.sample (F.parameters κ) (F.noise κ)),
    ← EnsembleLemmas.acceptProb_coins_equiv φ id]
  simp only [hverdict]
  rw [EnsembleLemmas.acceptProb_coins_fst, EnsembleLemmas.acceptProb_coins_fst]

/-! ## Single-bit security -/

/-- **Single-bit security of Regev encryption from decisional LWE** [Pei16, §5.2.1; Vad12,
Theorem 6.18]: if `DLWEAssumption F` and the width condition
`(n + 1) w + 2κ ≤ m` hold, then for every `NUPPT` distinguisher `D` of the encoded views,
`κ ↦ distAdv (realView P χ 0) (realView P χ 1) (fun v r => D(1^κ, encodeView v; r))` is
negligible. **Deviation:** over the raw `LWE.Family` and the encoded real views (key and one
ciphertext); the `BitPublicKeyScheme` instance and its honest efficiency are separate. The
width condition is that of the GSW analogue on PR #377, verbatim.

**Proof sketch.** `distAdv_encrypt_le` bounds the advantage by the two reductions' DLWE
advantages plus `2 · extractionError P`. By `exists_reductionMachine` the two advantages are
`F.advantageAt D₀ κ` and `F.advantageAt D₁ κ`, negligible under `DLWEAssumption F`; by
`two_extractionError_le` (with `F.modulus_le_pow` and the width condition) the error is at most
`2^{-κ}`, negligible by `negligible_two_pow_neg`. Conclude with `Negligible.add` and
`Negligible.mono`, the advantage being nonnegative. -/
theorem singleBitSecure_of_dlweAssumption (F : LWE.Family) (hF : LWE.DLWEAssumption F)
    (hm : ∀ κ, ((F.parameters κ).dimension + 1) * F.residueBits.eval κ + 2 * κ ≤
      (F.parameters κ).samples) (D : NUPPT) :
    Negligible fun κ => distAdv (realView (F.parameters κ) (F.noise κ) false)
      (realView (F.parameters κ) (F.noise κ) true)
      (fun v r => D.distinguisherL κ (encodeView (F.parameters κ) (F.residueBits.eval κ) v) r) := by
  obtain ⟨D₀, h₀⟩ := exists_reductionMachine F false D
  obtain ⟨D₁, h₁⟩ := exists_reductionMachine F true D
  have hsum : Negligible fun κ =>
      (F.advantageAt D₀ κ + F.advantageAt D₁ κ) + ((2 : ℝ)⁻¹) ^ κ :=
    (((LWE.dlweAssumption_iff F).mp hF D₀).add ((LWE.dlweAssumption_iff F).mp hF D₁)).add
      negligible_two_pow_neg
  refine hsum.mono ⟨0, fun κ _ => ?_⟩
  have hle := distAdv_encrypt_le (F.parameters κ) (F.noise κ) false true
    (fun v r => D.distinguisherL κ (encodeView (F.parameters κ) (F.residueBits.eval κ) v) r)
  rw [h₀ κ, h₁ κ] at hle
  have hext := two_extractionError_le (F.parameters κ) (F.residueBits.eval κ) κ
    (F.modulus_le_pow κ) (hm κ)
  have hnn : 0 ≤ distAdv (realView (F.parameters κ) (F.noise κ) false)
      (realView (F.parameters κ) (F.noise κ) true)
      (fun v r => D.distinguisherL κ (encodeView (F.parameters κ) (F.residueBits.eval κ) v) r) := by
    rw [distAdv_def]
    exact abs_nonneg _
  rw [abs_of_nonneg hnn, abs_of_nonneg (by linarith)]
  linarith

end TCSlib.Cryptography.Encryption.PublicKey.Regev
