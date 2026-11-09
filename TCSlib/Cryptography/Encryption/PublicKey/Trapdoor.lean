/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.HardCoreCollection
import TCSlib.Cryptography.Asymptotic.Sampling
import TCSlib.Cryptography.Encryption.PublicKey.EnsembleSecurity
import TCSlib.Cryptography.Encryption.PublicKey.TrapdoorPredictor
import TCSlib.Cryptography.Pseudorandom.GeneratorFromPermutation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Trapdoor bit encryption

This module builds the trapdoor construction of Algorithm 104.3. The predictor
machine for the security reduction is in `TrapdoorPredictor`. The Goldreich–Levin
bridge supplies the hard-core predicate under the encoding-width premise.

**Deviation.** The single-bit scheme samples `r ← D_i` with the collection's sampler.
It carries `⟨1^n, ⟨i, t⟩⟩` as the secret key, runs the trapdoor inverter on the
all-`true` coin string, and takes the predicate evaluator `H` as explicit data.
Honest sampling is the field `Collection.sample_spec`.

## Main definitions

* `TCSlib.Cryptography.Collection.PredEvaluator` is a polynomial-time evaluator
  of a predicate on a collection.
* `TCSlib.Cryptography.TrapdoorCollection.tdpBitScheme` packages the key generator,
  encryptor and decryptor of Algorithm 104.3.
* `TCSlib.Cryptography.pkPredictor` turns a ciphertext distinguisher into a predictor.

## Main results

* `TCSlib.Cryptography.Collection.HardCore.nonempty_predEvaluator` obtains a predicate
  evaluator by canonical decoding.
* `TCSlib.Cryptography.TrapdoorCollection.tdpBitScheme_singleBitSecure` proves single-bit
  security from one-wayness and a hard-core predicate.
* `TCSlib.Cryptography.TrapdoorCollection.OneWay.exists_glPad_singleBitSecure` supplies
  the predicate and its evaluator through Goldreich–Levin under the width premise `henc`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Algorithm 104.3 and Theorem 104.4.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Theorem 3.2 (the predictor from a distinguisher).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## Algorithm 104.3: a single-bit scheme from a trapdoor permutation with a hard-core bit -/

/-- A **polynomial-time evaluator of a predicate on a collection**: `H ⟨i, w⟩ = [h_i(x)]` for
every string `w` that decodes to `x ∈ D_i` (the efficiency clause of `Collection.HardCore`,
stated on every decodable string, such as the outputs of the sampler and of the trapdoor
inverter). Since
decoding is canonical (`Collection.encD_decD`, gate 03b ruling G3-1), every hard-core predicate
has one (`Collection.HardCore.nonempty_predEvaluator`). -/
structure Collection.PredEvaluator (F : Collection) (h : ∀ i, F.D i → Bool) where
  /-- The evaluator. -/
  H : List Bool → List Bool
  /-- The evaluator is polynomial-time. -/
  poly : PolyTimeComputable H
  /-- `H ⟨i, w⟩ = [h_i x]` whenever `w` decodes to `x`. -/
  spec : ∀ i w x, F.decD i w = some x → H (pairEncode i w) = [h i x]

/-- **Every hard-core predicate has a predicate evaluator**: the evaluator of `Collection.HardCore`,
correct on encodings, is correct on every decodable string under canonical decoding
(`Collection.HardCore.evaluator`). -/
theorem Collection.HardCore.nonempty_predEvaluator {F : Collection} {h : ∀ i, F.D i → Bool}
    (hh : F.HardCore h) : Nonempty (F.PredEvaluator h) :=
  let ⟨H, hH, hspec⟩ := hh.evaluator
  ⟨⟨H, hH, hspec⟩⟩

namespace TrapdoorCollection

variable (T : TrapdoorCollection)

/-- The raw key generator of [PS10, Algorithm 104.3] on `⟨⟨⟨1^n, []⟩, []⟩, r⟩`: run `Gen_T(1^n; r) = ⟨i, t⟩`
and output `⟨pk, sk⟩ = ⟨i, ⟨1^n, ⟨i, t⟩⟩⟩`. -/
def tdpGenFun (z : List Bool) : List Bool :=
  pairEncode (pairFstD (T.gen.output (NUPPT.layout (NUPPT.inParam z) [] [] (NUPPT.inCoins z))))
    (pairEncode (NUPPT.inParam z)
      (pairEncode (pairFstD (T.gen.output (NUPPT.layout (NUPPT.inParam z) [] [] (NUPPT.inCoins z))))
        (pairSndD (T.gen.output (NUPPT.layout (NUPPT.inParam z) [] [] (NUPPT.inCoins z))))))

/-- The raw key generator is polynomial-time. -/
theorem tdpGenFun_poly : PolyTimeComputable T.tdpGenFun :=
  have ho : PolyTimeComputable fun z =>
      T.gen.output (NUPPT.layout (NUPPT.inParam z) [] [] (NUPPT.inCoins z)) :=
    T.gen.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
      NUPPT.polyTimeComputable_inParam (polyTimeComputable_const []) (polyTimeComputable_const [])
      NUPPT.polyTimeComputable_inCoins)
  (polyTimeComputable_pairFstD.comp ho).pairEncode (NUPPT.polyTimeComputable_inParam.pairEncode
    ((polyTimeComputable_pairFstD.comp ho).pairEncode (polyTimeComputable_pairSndD.comp ho)))

/-- The raw encryptor of [PS10, Algorithm 104.3] on `⟨⟨⟨1^n, ⟨i, [m]⟩⟩, []⟩, s⟩`: sample
`w ← Sample(1^n, i; s)` and output `⟨eval ⟨i, w⟩, H ⟨i, w⟩ ⊕ [m]⟩ = ⟨f_i(r), b_i(r) ⊕ m⟩`. -/
def tdpEncFun (H : List Bool → List Bool) (z : List Bool) : List Bool :=
  pairEncode
    (T.eval (pairEncode (pairFstD (NUPPT.inArg z))
      (T.sample.output (NUPPT.layout (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)) [] (NUPPT.inCoins z)))))
    (List.zipWith xor
      (H (pairEncode (pairFstD (NUPPT.inArg z))
        (T.sample.output (NUPPT.layout (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)) [] (NUPPT.inCoins z)))))
      (pairSndD (NUPPT.inArg z)))

/-- The raw encryptor is polynomial-time (`polyTimeComputable_pairXor` for the mask). -/
theorem tdpEncFun_poly {H : List Bool → List Bool} (hH : PolyTimeComputable H) :
    PolyTimeComputable (T.tdpEncFun H) := by
  have hi := polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg
  have hiw := hi.pairEncode (T.sample.polyTimeComputable_output.comp
    (NUPPT.polyTimeComputable_layout NUPPT.polyTimeComputable_inParam hi
      (polyTimeComputable_const []) NUPPT.polyTimeComputable_inCoins))
  have h := (T.eval_poly.comp hiw).pairEncode (polyTimeComputable_pairXor.comp
    ((hH.comp hiw).pairEncode (polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg)))
  convert h using 1
  funext z
  simp only [tdpEncFun, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]

/-- The raw decryptor of [PS10, Algorithm 104.3] on `⟨⟨u, ⟨i, t⟩⟩, ⟨c₁, c₂⟩⟩`: run the trapdoor
inverter `Inv(u, ⟨t, c₁⟩)` on the all-`true` coin string of length `coins(|u|)` and output
`H ⟨i, Inv(…)⟩ ⊕ c₂ = b_i(f_i^{-1}(c₁)) ⊕ c₂`. -/
def tdpDecFun (H : List Bool → List Bool) (z : List Bool) : List Bool :=
  List.zipWith xor
    (H (pairEncode (pairFstD (pairSndD (pairFstD z)))
      (T.inv.output (NUPPT.layout (pairFstD (pairFstD z))
        (pairEncode (pairSndD (pairSndD (pairFstD z))) (pairFstD (pairSndD z))) []
        (List.replicate (T.inv.coins.eval (pairFstD (pairFstD z)).length) true)))))
    (pairSndD (pairSndD z))

/-- The raw decryptor is polynomial-time (`polyTimeComputable_unaryPoly` for the coin string). -/
theorem tdpDecFun_poly {H : List Bool → List Bool} (hH : PolyTimeComputable H) :
    PolyTimeComputable (T.tdpDecFun H) := by
  have hsk := polyTimeComputable_pairFstD
  have hu := polyTimeComputable_pairFstD.comp hsk
  have hi := polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp hsk)
  have ht := polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp hsk)
  have hc₁ := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hc₂ := polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hw := T.inv.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout hu
    (ht.pairEncode hc₁) (polyTimeComputable_const [])
    ((polyTimeComputable_unaryPoly T.inv.coins).comp hu))
  have h := polyTimeComputable_pairXor.comp ((hH.comp (hi.pairEncode hw)).pairEncode hc₂)
  convert h using 1
  funext z
  simp only [tdpDecFun, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]

/-- The key generator of [PS10, Algorithm 104.3]: `Gen_T`'s coins, output `⟨i, ⟨1^n, ⟨i, t⟩⟩⟩`. -/
noncomputable def tdpGen : NUPPT := NUPPT.ofPolyTimeUniform T.tdpGenFun_poly T.gen.coins

/-- The encryptor of [PS10, Algorithm 104.3] with the predicate evaluator `H`: the sampler's coins. -/
noncomputable def tdpEnc {h : ∀ i, T.D i → Bool} (E : T.toCollection.PredEvaluator h) : NUPPT :=
  NUPPT.ofPolyTimeUniform (T.tdpEncFun_poly E.poly) T.sample.coins

/-- The key generator has the coins of `Gen_T`. -/
theorem coins_tdpGen : T.tdpGen.coins = T.gen.coins := by
  unfold tdpGen
  exact NUPPT.coins_ofPolyTimeUniform _ _

/-- **The key generator runs on the coins of `Gen_T`**: the published equivalence
`T.tdpGen.Coins n ≃ T.gen.Coins n` (`NUPPT.coinsCongr` along `coins_tdpGen`). -/
noncomputable def tdpGen_coinsEquiv (n : ℕ) : T.tdpGen.Coins n ≃ T.gen.Coins n :=
  NUPPT.coinsCongr T.coins_tdpGen n

/-- The coin equivalence keeps the coin string:
`List.ofFn (T.tdpGen_coinsEquiv n r) = List.ofFn r`. -/
theorem tdpGen_coinsEquiv_ofFn (n : ℕ) (r : T.tdpGen.Coins n) :
    List.ofFn (T.tdpGen_coinsEquiv n r) = List.ofFn r :=
  NUPPT.coinsCongr_ofFn T.coins_tdpGen n r

/-- The encryptor has the coins of the sampler. -/
theorem coins_tdpEnc {h : ∀ i, T.D i → Bool} (E : T.toCollection.PredEvaluator h) :
    (T.tdpEnc E).coins = T.sample.coins := by
  unfold tdpEnc
  exact NUPPT.coins_ofPolyTimeUniform _ _

/-- **The encryptor runs on the coins of the sampler**: the published equivalence
`(T.tdpEnc E).Coins n ≃ T.sample.Coins n` (`NUPPT.coinsCongr` along `coins_tdpEnc`). -/
noncomputable def tdpEnc_coinsEquiv {h : ∀ i, T.D i → Bool} (E : T.toCollection.PredEvaluator h)
    (n : ℕ) : (T.tdpEnc E).Coins n ≃ T.sample.Coins n :=
  NUPPT.coinsCongr (T.coins_tdpEnc E) n

/-- The coin equivalence keeps the coin string:
`List.ofFn (T.tdpEnc_coinsEquiv E n s) = List.ofFn s`. -/
theorem tdpEnc_coinsEquiv_ofFn {h : ∀ i, T.D i → Bool} (E : T.toCollection.PredEvaluator h)
    (n : ℕ) (s : (T.tdpEnc E).Coins n) : List.ofFn (T.tdpEnc_coinsEquiv E n s) = List.ofFn s :=
  NUPPT.coinsCongr_ofFn (T.coins_tdpEnc E) n s

/-- Unfolding: `Gen(1^n; r) = ⟨i, ⟨1^n, ⟨i, t⟩⟩⟩` with `⟨i, t⟩ = Gen_T(1^n; φ r)`, the coins read
through `φ = T.tdpGen_coinsEquiv n`. -/
theorem tdpGen_runAt (n : ℕ) (r : T.tdpGen.Coins n) :
    T.tdpGen.runAt n [] r =
      pairEncode (T.index n (T.tdpGen_coinsEquiv n r)) (pairEncode (List.replicate n true)
        (pairEncode (T.index n (T.tdpGen_coinsEquiv n r)) (T.trap n (T.tdpGen_coinsEquiv n r)))) := by
  rw [Collection.index_eq, Collection.trap_eq, T.gen_uniform.runAt_eq, T.tdpGen_coinsEquiv_ofFn,
    NUPPT.runAt_eq]
  unfold tdpGen
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp only [tdpGenFun, NUPPT.inParam_eq, NUPPT.inCoins_eq, NUPPT.advInput_eq, pairFstD_pairEncode,
    pairSndD_pairEncode]
  rw [NUPPT.layout_eq]

/-- Unfolding: `Enc(1^n, ⟨i, [b]⟩; s) = ⟨eval ⟨i, w⟩, H ⟨i, w⟩ ⊕ [b]⟩` with
`w = Sample(1^n, i; φ s)`, the coins read through `φ = T.tdpEnc_coinsEquiv E n`. -/
theorem tdpEnc_runAt {h : ∀ i, T.D i → Bool} (E : T.toCollection.PredEvaluator h) (n : ℕ)
    (i : List Bool) (b : Bool) (s : (T.tdpEnc E).Coins n) :
    (T.tdpEnc E).runAt n (pairEncode i [b]) s =
      pairEncode (T.eval (pairEncode i (T.sample.runAt n i (T.tdpEnc_coinsEquiv E n s))))
        (List.zipWith xor (E.H (pairEncode i (T.sample.runAt n i (T.tdpEnc_coinsEquiv E n s))))
          [b]) := by
  rw [T.sample_uniform.runAt_eq, T.tdpEnc_coinsEquiv_ofFn, NUPPT.runAt_eq]
  unfold tdpEnc
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp only [tdpEncFun, NUPPT.inParam_eq, NUPPT.inArg_eq, NUPPT.inCoins_eq, NUPPT.advInput_eq,
    pairFstD_pairEncode, pairSndD_pairEncode]
  rw [NUPPT.layout_eq]

/-- Unfolding: `Dec(⟨⟨1^n, ⟨i, t⟩⟩, ⟨c₁, c₂⟩⟩) = H ⟨i, Inv(1^n, ⟨t, c₁⟩; 1^{coins n})⟩ ⊕ c₂`. -/
theorem tdpDecFun_apply (H : List Bool → List Bool) (n : ℕ) (i t c₁ c₂ : List Bool) :
    T.tdpDecFun H (pairEncode (pairEncode (List.replicate n true) (pairEncode i t)) (pairEncode c₁ c₂)) =
      List.zipWith xor (H (pairEncode i (T.inv.runAt n (pairEncode t c₁) fun _ => true))) c₂ := by
  rw [T.inv_uniform.runAt_eq, NUPPT.advInput_eq, List.ofFn_const, NUPPT.coinLen_eq]
  simp only [tdpDecFun, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
    NUPPT.layout_eq]

/-- **The single-bit scheme of [PS10, Algorithm 104.3]** from a collection of trapdoor
permutations `T` with a predicate `h` (its hard-core bit), given a polynomial-time evaluator `E`
of `h`: `Gen(1^n) = ⟨i, ⟨1^n, ⟨i, t⟩⟩⟩` with `⟨i, t⟩ ← Gen_T(1^n)`,
`Enc_i(m) = ⟨f_i(r), h_i(r) ⊕ m⟩` for `r ← Sample(1^n, i)`, `Dec(c₁, c₂) = h_i(f_i^{-1}(c₁)) ⊕ c₂`.

**Deviation:** `r ← D_i` through the collection's sampler (the text's `r ← {0,1}^n`); the secret
key carries `1^n` and `i` (the text's `f_i^{-1}` "knows" `i`); the inverter runs on the all-`true`
coin string (`inv_spec` holds for every coin string); `E` is explicit data. Repair (run-3 audit
P3-1): the former hypothesis `hS : T.toCollection.EvalSampled` is dropped, being
`T.toCollection.evalSampled` (the field `Collection.sample_spec`).

**Proof sketch** (of correctness). `tdpGen_runAt`, `tdpEnc_runAt`, `tdpDecFun_apply`;
`T.toCollection.evalSampled` gives `x` with `decD i w = some x` and
`eval ⟨i, w⟩ = f_i x = encD i (perm i x)` (`f_perm`);
`inv_spec` at `perm i x` decodes the inverter's answer to `x` (`Equiv.symm_apply_apply`); `E.spec`
twice gives `H = [h_i x]` on both strings, and `a ⊕ (a ⊕ b) = b`. -/
noncomputable def tdpBitScheme {h : ∀ i, T.D i → Bool} (E : T.toCollection.PredEvaluator h) :
    BitPublicKeyScheme where
  gen := T.tdpGen
  enc := T.tdpEnc E
  dec := T.tdpDecFun E.H
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  enc_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  dec_poly := T.tdpDecFun_poly E.poly
  correct := by
    intro n b rg' re'
    rw [tdpGen_runAt]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode]
    rw [tdpEnc_runAt, tdpDecFun_apply]
    set rg := T.tdpGen_coinsEquiv n rg'
    set re := T.tdpEnc_coinsEquiv E n re'
    obtain ⟨x, hx, hev⟩ := (Collection.evalSampled_iff _).1 T.toCollection.evalSampled n rg re
    rw [hev, T.f_perm]
    have hinv : T.decD (T.index n rg) (T.inv.runAt n
        (pairEncode (T.trap n rg) (T.encD (T.index n rg) (T.perm (T.index n rg) x))) fun _ => true) =
        some x := by
      rw [T.inv_eq_encD n rg (T.perm _ x) (fun _ => true), Equiv.symm_apply_apply]
      exact T.decD_encD _ x
    rw [E.spec _ _ _ hinv, E.spec _ _ _ hx]
    cases h (T.index n rg) x <;> cases b <;> rfl

end TrapdoorCollection

/-! ## Lem-104.a: from a ciphertext distinguisher to a predictor of the hard-core bit -/

/-- The predictor `A'` of [PS10, Theorem 104.4, proof] built from a distinguisher `D` of
`(f(r), b(r))` versus `(f(r), ¬b(r))` (the encryptions of `0` and `1`): on input `y = f(r)`, draw
`c ← {0,1}` and coins for `D`, output `c` if `D(y, c)` accepts and `1 − c` otherwise (negated when
`flip`); this is `owpPredictor` with the pass-through component removed. -/
def pkPredictor {α ρ : Type*} (D : α × Bool → ρ → Bool) (flip : Bool) : α → Bool × ρ → Bool :=
  fun y c => xor (if D (y, c.1) c.2 then c.1 else !c.1) flip

/-- The predictor is `owpPredictor` on `α × Unit`. -/
private theorem predProb_pkPredictor_eq {α ρ : Type*} [Fintype α] [Fintype ρ] (f : α ≃ α)
    (B : α → Bool) (D : α × Bool → ρ → Bool) (flip : Bool) :
    predProb f B (pkPredictor D flip) =
      predProb (owpPair (β := Unit) f) (fun w => B w.1)
        (owpPredictor (fun v : α × Unit × Bool => fun r => D (v.1, v.2.2) r) flip) := by
  simp only [predProb_def]
  exact uprob_eq_of_equiv ((Equiv.prodPUnit α).symm.prodCongr (Equiv.refl _)) fun _ => Iff.rfl

/-- `acceptProb` of the generator `owpGen` on `α × Unit` is that of `(f(x), B(x))`. -/
private theorem acceptProb_owpGen_unit {α ρ : Type*} [Fintype α] [Fintype ρ] (f : α ≃ α)
    (B : α → Bool) (D : α × Bool → ρ → Bool) :
    acceptProb (owpGen (β := Unit) f fun w => B w.1) (fun v : α × Unit × Bool => fun r => D (v.1, v.2.2) r) =
      acceptProb (fun x => (f x, B x)) D := by
  simp only [acceptProb_def]
  exact uprob_eq_of_equiv ((Equiv.prodPUnit α).prodCongr (Equiv.refl _)) fun _ => Iff.rfl

/-- `acceptProb` of `owpGenNot` on `α × Unit` is that of `(f(x), ¬B(x))`. -/
private theorem acceptProb_owpGenNot_unit {α ρ : Type*} [Fintype α] [Fintype ρ] (f : α ≃ α)
    (B : α → Bool) (D : α × Bool → ρ → Bool) :
    acceptProb (owpGenNot (β := Unit) f fun w => B w.1) (fun v : α × Unit × Bool => fun r => D (v.1, v.2.2) r) =
      acceptProb (fun x => (f x, !B x)) D := by
  simp only [acceptProb_def]
  exact uprob_eq_of_equiv ((Equiv.prodPUnit α).prodCongr (Equiv.refl _)) fun _ => Iff.rfl

/-- **The predictor `pkPredictor D false` predicts `B` from `f(x)` with probability exactly
`1/2 + (Pr[D(f(x), B(x)) = 1] − Pr[D(f(x), ¬B(x)) = 1]) / 2`** (Lem-104.a, signed form; the
identity behind [PS10, Theorem 104.4, proof] and [Gar26, Theorem 3.2]). The sign is uniform over
the index in the collection setting, so the forms with a fixed `flip` average over `Gen`'s coins.

**Proof sketch.** `predProb_owpPredictor_false` on `α × Unit` (`predProb_pkPredictor_eq`,
`acceptProb_owpGen_unit`, `acceptProb_owpGenNot_unit`). -/
theorem predProb_pkPredictor_false {α ρ : Type*} [Fintype α] [Fintype ρ] [Nonempty α] [Nonempty ρ]
    (f : α ≃ α) (B : α → Bool) (D : α × Bool → ρ → Bool) :
    predProb f B (pkPredictor D false) =
      1 / 2 + (acceptProb (fun x => (f x, B x)) D - acceptProb (fun x => (f x, !B x)) D) / 2 := by
  rw [predProb_pkPredictor_eq, predProb_owpPredictor_false, acceptProb_owpGen_unit,
    acceptProb_owpGenNot_unit]

/-- **The flipped predictor `pkPredictor D true` predicts `B` with probability exactly
`1/2 − (Pr[D(f(x), B(x)) = 1] − Pr[D(f(x), ¬B(x)) = 1]) / 2`** (Lem-104.a, the other sign). -/
theorem predProb_pkPredictor_true {α ρ : Type*} [Fintype α] [Fintype ρ] [Nonempty α] [Nonempty ρ]
    (f : α ≃ α) (B : α → Bool) (D : α × Bool → ρ → Bool) :
    predProb f B (pkPredictor D true) =
      1 / 2 - (acceptProb (fun x => (f x, B x)) D - acceptProb (fun x => (f x, !B x)) D) / 2 := by
  rw [predProb_pkPredictor_eq, predProb_owpPredictor_true, acceptProb_owpGen_unit,
    acceptProb_owpGenNot_unit]

/-- **Lem-104.a**: a distinguisher `D` of `(f(r), b(r))` versus `(f(r), ¬b(r))` with advantage `ε`
yields, for one choice of `flip`, a predictor of `b` from `f(r)` with success exactly `1/2 + ε/2`
([PS10, Theorem 104.4, proof: "we can now use `A` to construct a machine `A'` that predicts the
hard-core predicate"]; [Gar26, Theorem 3.2]). -/
theorem exists_pkPredictor {α ρ : Type*} [Fintype α] [Fintype ρ] [Nonempty α] [Nonempty ρ]
    (f : α ≃ α) (B : α → Bool) (D : α × Bool → ρ → Bool) :
    ∃ flip : Bool, predProb f B (pkPredictor D flip) =
      1 / 2 + distAdv (fun x => (f x, B x)) (fun x => (f x, !B x)) D / 2 := by
  simp only [distAdv_def]
  rcases le_total 0 (acceptProb (fun x => (f x, B x)) D - acceptProb (fun x => (f x, !B x)) D) with
    h | h
  · exact ⟨false, by rw [predProb_pkPredictor_false, abs_of_nonneg h]⟩
  · exact ⟨true, by rw [predProb_pkPredictor_true, abs_of_nonpos h]; ring⟩

/-! ## Theorem 104.4 -/

/-- The sampled element of `D_i` behind the honest ciphertext: the decoding of
`Sample(1^n, i; s)` (always `some`, by `Collection.sample_spec`), with the default as fallback. -/
private def tdpSampled (T : TrapdoorCollection) (n : ℕ) (r : T.gen.Coins n) (s : T.sample.Coins n) :
    T.D (T.index n r) :=
  (T.decD (T.index n r) (T.sample.runAt n (T.index n r) s)).getD default

/-- **The honest ciphertext of Algorithm 104.3** is `⟨i, ⟨f_i(x), [h_i(x) ⊕ b]⟩⟩` for the sampled
element `x` (`tdpGen_runAt`, `tdpEnc_runAt`, `Collection.evalSampled`, `E.spec`, `f_perm`). -/
private theorem tdpBitScheme_pkEncDist (T : TrapdoorCollection) {h : ∀ i, T.D i → Bool}
    (E : T.toCollection.PredEvaluator h) (n : ℕ) (b : Bool) (r₀ : T.tdpGen.Coins n)
    (s₀ : (T.tdpEnc E).Coins n) :
    (T.tdpBitScheme E).pkEncDist n b (r₀, s₀) =
      pairEncode (T.index n (T.tdpGen_coinsEquiv n r₀))
        (pairEncode (T.encD _ (T.perm _ (tdpSampled T n (T.tdpGen_coinsEquiv n r₀)
          (T.tdpEnc_coinsEquiv E n s₀))))
        [xor (h _ (tdpSampled T n (T.tdpGen_coinsEquiv n r₀) (T.tdpEnc_coinsEquiv E n s₀))) b]) := by
  rw [BitPublicKeyScheme.pkEncDist_eq]
  show pairEncode (pairFstD (T.tdpGen.runAt n [] r₀))
      ((T.tdpEnc E).runAt n (pairEncode (pairFstD (T.tdpGen.runAt n [] r₀)) [b]) s₀) = _
  rw [TrapdoorCollection.tdpGen_runAt]
  simp only [pairFstD_pairEncode]
  set r := T.tdpGen_coinsEquiv n r₀
  set s := T.tdpEnc_coinsEquiv E n s₀
  obtain ⟨x, hx, hev⟩ := (Collection.evalSampled_iff _).1 T.toCollection.evalSampled n r s
  rw [TrapdoorCollection.tdpEnc_runAt, hev, T.f_perm, E.spec _ _ _ hx]
  simp only [tdpSampled, hx, Option.getD_some]
  rfl

/-- **[PS10, Theorem 104.4]: the scheme of Algorithm 104.3 is a secure single-bit public-key
encryption scheme** when `T` is a collection of one-way trapdoor permutations and `h` is a
hard-core predicate for it.

**Deviation:** the hypothesis includes the hard-core predicate `hHC` (the text's "if trapdoor
permutations exist" omits it; `TrapdoorCollection.OneWay.glPad_hardCore` supplies one from
trapdoor permutations whose generated indices encode elements in exactly `m(n)` bits (`henc`,
which no candidate of the library satisfies as parametrized; see `Collection.glPad`), see
`OneWay.exists_glPad_singleBitSecure`); the proof's "`D`"
in the display after the prediction lemma is the predictor `A`.

**Proof sketch.** Fix a non-uniform PPT `D`; let `μ n` be its advantage between
`pkEncDist n false` and `pkEncDist n true` (by `singleBitSecure_iff` it suffices to bound `μ`).
For `flip ∈ {false, true}` build the machine `A_flip` with coins `const 1 + D.coins` and advice
`D.advice`: on `⟨1^n, ⟨i, y⟩⟩` it reads the coin `c`, runs `D` on `⟨1^n, ⟨i, ⟨y, [c]⟩⟩⟩` with the
remaining coins (`NUPPT.exists_split (const 1)`, `NUPPT.exists_comp` with `pre` the re-pairing),
and outputs `[c ⊕ verdict ⊕ flip]` (`polyTimeComputable_pairEq` for the verdict `= [true]`,
`polyTimeComputable_pairXor`) — the text's `A'` composed with the prediction lemma's sign choice.
`hHC.2 A_flip` gives a negligible `ε_flip` with, for all `n`,
`E_r[Pr_{x, c, ρ}[A_flip(1^n, ⟨i, f_i x⟩) = h_i x]] ≤ 1/2 + ε_flip n`. For a fixed `r` (index
`i = index n r`), the inner probability is `predProb (perm i) (h i) (pkPredictor D_i flip)` with
`D_i (y, c) ρ := D.distinguisherL n ⟨i, ⟨encD i y, [c]⟩⟩ ρ` (`f_perm`, `uprob_comp_equiv` on the
coin split), which `predProb_pkPredictor_false/true` evaluates as
`1/2 ± (Pr[D_i(f_i x, h_i x)] − Pr[D_i(f_i x, ¬h_i x)])/2` over the ideal uniform `x ∈ D_i`.
Averaging over `r` (`OneWay.uexp_add`, `uexp_const`) gives
`1/2 ± (P₀ − P₁)/2 ≤ 1/2 + ε_flip n` where `P_b` is `D`'s acceptance of `⟨i, ⟨f_i x, [h_i x ⊕ b]⟩⟩`
with ideal `x`. By `tdpGen_runAt`/`tdpEnc_runAt` the honest sample `pkEncDist n b` is the same
string with `x` replaced by the sampler's output `decD i (Sample(1^n, i; s))`
(`T.toCollection.evalSampled`, `E.spec`), so `|acceptProb (pkEncDist n b) D − P_b| ≤ δ n` by
`hT.sampleClose = ⟨δ, hδ, hS'⟩` and `StatClose.abs_uprob_sub_le_prod` averaged over `r`
(`OneWay.uexp_mono`). Hence `μ n ≤ 2 (ε_false n + ε_true n) + 2 δ n` for every `n` (the sign of
`P₀ − P₁` selects the flip), negligible by `Negligible.add`, `Negligible.const_mul`,
`Negligible.mono`. (Formally: the machines are `tdpPredictor D flip`, the coin split is
`predCoins`, the per-index identity is `uprob_tdpPredictor`, the honest ciphertext is
`tdpBitScheme_pkEncDist` and the bound is `2 δ(n) + 2 (|ε_false(n)| + |ε_true(n)|)`.) -/
theorem TrapdoorCollection.tdpBitScheme_singleBitSecure (T : TrapdoorCollection)
    {h : ∀ i, T.D i → Bool} (E : T.toCollection.PredEvaluator h)
    (hT : T.OneWay) (hHC : T.toCollection.HardCore h) : (T.tdpBitScheme E).SingleBitSecure := by
  rw [BitPublicKeyScheme.singleBitSecure_iff]
  intro D
  obtain ⟨δ, hδ, hδS⟩ := ((TrapdoorCollection.oneWay_iff T).1 hT).sampleClose
  replace hδS := (Collection.sampleClose_iff _ _).1 hδS
  obtain ⟨εf, hεf, hAf⟩ := ((Collection.hardCore_iff _ _).1 hHC).2 (tdpPredictor D false)
  obtain ⟨εt, hεt, hAt⟩ := ((Collection.hardCore_iff _ _).1 hHC).2 (tdpPredictor D true)
  -- the concrete distinguisher of `(f_i(x), c)` at the index `i = index n r`
  let Di : ∀ n (r : T.gen.Coins n), T.D (T.index n r) × Bool → D.Coins n → Bool :=
    fun n r yc ρ =>
      D.distinguisherL n (pairEncode (T.index n r) (pairEncode (T.encD _ yc.1) [yc.2])) ρ
  -- the honest acceptance probability is within `δ n` of the ideal one
  have hclose : ∀ n (b : Bool),
      |acceptProb ((T.tdpBitScheme E).pkEncDist n b) (D.distinguisherL n) -
        uexp (fun r : T.gen.Coins n =>
          acceptProb (fun x : T.D (T.index n r) => (T.perm _ x, xor (h _ x) b)) (Di n r))| ≤ δ n := by
    intro n b
    have e1 : acceptProb ((T.tdpBitScheme E).pkEncDist n b) (D.distinguisherL n) =
        uexp fun r : T.gen.Coins n => uprob fun w : T.sample.Coins n × D.Coins n =>
          D.distinguisherL n (pairEncode (T.index n r)
            (pairEncode (T.encD _ (T.perm _ (tdpSampled T n r w.1)))
              [xor (h _ (tdpSampled T n r w.1)) b])) w.2 = true := by
      rw [acceptProb_def, ← uprob_comp_equiv ((Equiv.prodAssoc (T.gen.Coins n) (T.sample.Coins n)
        (D.Coins n)).symm.trans (((T.tdpGen_coinsEquiv n).symm.prodCongr
          (T.tdpEnc_coinsEquiv E n).symm).prodCongr (Equiv.refl _))), uprob_prod]
      congr 1
      funext r
      congr 1
      funext w
      obtain ⟨s, ρ⟩ := w
      simp only [Equiv.trans_apply, Equiv.prodAssoc_symm_apply, Equiv.prodCongr_apply,
        Prod.map_apply, Equiv.refl_apply]
      rw [tdpBitScheme_pkEncDist]
      generalize hr' : (T.tdpGen_coinsEquiv n) ((T.tdpGen_coinsEquiv n).symm r) = r'
      generalize hs' : (T.tdpEnc_coinsEquiv E n) ((T.tdpEnc_coinsEquiv E n).symm s) = s'
      rw [Equiv.apply_symm_apply] at hr' hs'
      subst hr' hs'
      rfl
    rw [e1]
    refine abs_uexp_sub_le (hδS n (fun _ => false)).nonneg fun r => ?_
    have hs := (hδS n r).abs_uprob_sub_le_prod
      fun (o : Option (T.D (T.index n r))) (ρ : D.Coins n) =>
        D.distinguisherL n (pairEncode (T.index n r)
          (pairEncode (T.encD _ (T.perm _ (o.getD default))) [xor (h _ (o.getD default)) b])) ρ = true
    simp only [Option.getD_some] at hs
    rw [acceptProb_def]
    exact hs
  -- the prediction experiments of the two predictor machines
  have key : ∀ n (flip : Bool) (r : T.gen.Coins n),
      uprob (fun z : T.D (T.index n r) × (tdpPredictor D flip).Coins n =>
        (tdpPredictor D flip).distinguisherL n (pairEncode (T.index n r) (T.f _ z.1)) z.2 =
          h (T.index n r) z.1) =
      predProb (T.perm (T.index n r)) (h (T.index n r)) (pkPredictor (Di n r) flip) := by
    intro n flip r
    simp only [T.f_perm]
    rw [predProb_def]
    exact uprob_tdpPredictor D flip n (T.index n r) (T.perm _) (h _) (T.encD _)
  have hf : ∀ n, uexp (fun r : T.gen.Coins n =>
      acceptProb (fun x : T.D (T.index n r) => (T.perm _ x, h _ x)) (Di n r)) -
      uexp (fun r : T.gen.Coins n =>
        acceptProb (fun x : T.D (T.index n r) => (T.perm _ x, !h _ x)) (Di n r)) ≤ 2 * εf n := by
    intro n
    have := hAf n
    have e : uexp (fun r : T.gen.Coins n => 1 / 2 +
        (acceptProb (fun x : T.D (T.index n r) => (T.perm _ x, h _ x)) (Di n r) -
          acceptProb (fun x : T.D (T.index n r) => (T.perm _ x, !h _ x)) (Di n r)) / 2) ≤
        1 / 2 + εf n := by
      refine le_of_eq_of_le ?_ this
      congr 1
      funext r
      rw [← predProb_pkPredictor_false (T.perm _) (h _) (Di n r), ← key n false r]
    rw [uexp_half_add] at e
    linarith
  have ht : ∀ n, uexp (fun r : T.gen.Coins n =>
      acceptProb (fun x : T.D (T.index n r) => (T.perm _ x, !h _ x)) (Di n r)) -
      uexp (fun r : T.gen.Coins n =>
        acceptProb (fun x : T.D (T.index n r) => (T.perm _ x, h _ x)) (Di n r)) ≤ 2 * εt n := by
    intro n
    have := hAt n
    have e : uexp (fun r : T.gen.Coins n => 1 / 2 -
        (acceptProb (fun x : T.D (T.index n r) => (T.perm _ x, h _ x)) (Di n r) -
          acceptProb (fun x : T.D (T.index n r) => (T.perm _ x, !h _ x)) (Di n r)) / 2) ≤
        1 / 2 + εt n := by
      refine le_of_eq_of_le ?_ this
      congr 1
      funext r
      rw [← predProb_pkPredictor_true (T.perm _) (h _) (Di n r), ← key n true r]
    rw [uexp_half_sub] at e
    linarith
  -- the negligible bound `2 δ + 2 (|ε_false| + |ε_true|)`
  refine ((hδ.const_mul 2).add (((hεf.mono ⟨0, fun n _ => (abs_abs _).le⟩).add
    (hεt.mono ⟨0, fun n _ => (abs_abs _).le⟩)).const_mul 2)).mono ⟨0, fun n _ => ?_⟩
  have hc0 := hclose n false
  have hc1 := hclose n true
  simp only [Bool.xor_false, Bool.xor_true] at hc0 hc1
  rw [distAdv_def]
  set A₀ := acceptProb ((T.tdpBitScheme E).pkEncDist n false) (D.distinguisherL n) with hA₀
  set A₁ := acceptProb ((T.tdpBitScheme E).pkEncDist n true) (D.distinguisherL n) with hA₁
  set Qa := uexp (fun r : T.gen.Coins n =>
    acceptProb (fun x : T.D (T.index n r) => (T.perm _ x, h _ x)) (Di n r)) with hQa
  set Qb := uexp (fun r : T.gen.Coins n =>
    acceptProb (fun x : T.D (T.index n r) => (T.perm _ x, !h _ x)) (Di n r)) with hQb
  have hmid : |Qa - Qb| ≤ 2 * (|εf n| + |εt n|) := by
    have h1 := hf n
    have h2 := ht n
    have h3 := le_abs_self (εf n)
    have h4 := le_abs_self (εt n)
    have h5 := abs_nonneg (εf n)
    have h6 := abs_nonneg (εt n)
    rw [abs_sub_le_iff]
    constructor <;> linarith
  have hδ0 : 0 ≤ δ n := (hδS n (fun _ => false)).nonneg
  have htri1 := abs_sub_le A₀ Qa A₁
  have htri2 := abs_sub_le Qa Qb A₁
  have hpos : 0 ≤ 2 * δ n + 2 * (|εf n| + |εt n|) := by positivity
  rw [abs_of_nonneg hpos]
  show |(|A₀ - A₁|)| ≤ _
  rw [abs_abs, abs_sub_comm A₁ Qb] at *
  linarith

/-- **Trapdoor permutations give a secure single-bit public-key encryption scheme** — the text's
reading of [PS10, Theorem 104.4] with the hard-core bit supplied by Goldreich–Levin
([PS10, Theorem 87.3], collection form): for a collection of one-way trapdoor permutations `T`
with encoding length `m(n)` at generated indices, the scheme of Algorithm 104.3 for the padded
collection `T.glPad m` with the predicate `⟨x, r⟩` (read through the published domain
equivalence `T.glPad_domEquiv`) is single-bit secure (given its predicate evaluator, which always
exists: `OneWay.exists_glPad_singleBitSecure`). The cost of `henc`: no candidate of the library
satisfies it as parametrized (see `Collection.glPad`). -/
theorem TrapdoorCollection.OneWay.glPad_tdpBitScheme_singleBitSecure {T : TrapdoorCollection}
    (m : PolyExpr)
    (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n)
    (hT : T.OneWay)
    (E : (T.glPad m henc).toCollection.PredEvaluator
      fun i z => T.glBit i (T.glPad_domEquiv m henc i z)) :
    ((T.glPad m henc).tdpBitScheme E).SingleBitSecure :=
  (T.glPad m henc).tdpBitScheme_singleBitSecure E (hT.glPad m henc)
    (hT.glPad_hardCore_domEquiv m henc)

/-- **Trapdoor permutations give a secure single-bit public-key encryption scheme**, without a
supplied evaluator — the text's reading of [PS10, Theorem 104.4] through Goldreich–Levin
([PS10, Theorem 87.3], collection form): for a collection of one-way trapdoor permutations `T`
with encoding length `m(n)` at generated indices (`henc`; see `Collection.glPad` for its cost),
some predicate evaluator `E` of `⟨x, r⟩` (read through `T.glPad_domEquiv`) on `T.glPad m` makes
the scheme of Algorithm 104.3 single-bit secure. The evaluator comes from the hard-core predicate
(`TrapdoorCollection.OneWay.glPad_hardCore_domEquiv`, `Collection.HardCore.nonempty_predEvaluator`,
canonical decoding). -/
theorem TrapdoorCollection.OneWay.exists_glPad_singleBitSecure {T : TrapdoorCollection}
    (m : PolyExpr)
    (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n)
    (hT : T.OneWay) :
    ∃ E : (T.glPad m henc).toCollection.PredEvaluator
        fun i z => T.glBit i (T.glPad_domEquiv m henc i z),
      ((T.glPad m henc).tdpBitScheme E).SingleBitSecure :=
  let ⟨E⟩ := (hT.glPad_hardCore_domEquiv m henc).nonempty_predEvaluator
  ⟨E, hT.glPad_tdpBitScheme_singleBitSecure m henc E⟩

end TCSlib.Cryptography
