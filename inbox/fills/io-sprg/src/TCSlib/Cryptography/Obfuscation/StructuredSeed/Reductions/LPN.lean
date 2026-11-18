/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Hybrids
import TCSlib.Cryptography.Asymptotic.Realization

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The explicit advice-based LPN reduction

## Main definitions

* `Params.LPNChal` and `lpnEnc` are exactly the canonical LWE-family challenge and encoding.
* `Params.LPNAdvice` retains an inhabited sentinel hop and the values fixed by averaging.
* `Params.lpnPre` prepares the hybrid challenge without sampling or evaluating the PRG.
* `Params.lpnRed` invokes the adversary on that preprocessing and a prefix of its coins.

## Main results

* `encLPNAdvice_length_le` gives an explicit polynomial advice bound.
* `lpn_hop` bounds any chosen hybrid hop for every machine realizing the explicit reduction.

## References

* [JLS26] A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from Well-Founded
  Assumptions*, J. ACM 73(1), Article 1, February 2026, Lemma 4.2, p. 19.
* [PS10] R. Pass, A. Shelat, *A Course in Cryptography*, 2010, Definition 26.8.

**Deviations.** Dv3 uses the transposed LPN family at its own dimension. Dv8 retains
independent bucket placements. Dv9 puts the schedule's public prime first in advice.
Dv12 fixes all averaged values and the hop in non-uniform advice; the reduction neither
samples nor evaluates a Boolean PRG. Dv14 proves function-level reductions, with named
preprocessing targets supplying their machines later. Dv15 uses explicit finite-coordinate
casts and equivalences. Dv16 reuses shared `RealizesOn`, which constrains encoded challenges
and coin lists of the layout length only; this strengthens every-realiser security.
-/

namespace TCSlib.Cryptography.Obfuscation.StructuredSeed

open Complexity Turing
open scoped BigOperators

namespace Params

/-- The LPN challenge is exactly the canonical challenge of the construction's LWE-family view
[JLS26, Lemma 4.2, p. 19]. Dv3 uses the family's independent dimension L and matrix orientation. -/
abbrev LPNChal (P : Params) (π : PrimeSchedule) (L : ℕ) : Type :=
  Matrix (Fin ((P.lpnFamily_raw π).toLWE.parameters L).samples)
      (Fin ((P.lpnFamily_raw π).toLWE.parameters L).dimension)
      (ZMod ((P.lpnFamily_raw π).toLWE.parameters L).modulus) ×
    (Fin ((P.lpnFamily_raw π).toLWE.parameters L).samples →
      ZMod ((P.lpnFamily_raw π).toLWE.parameters L).modulus)

/-- The canonical challenge is its displayed LWE matrix/value product. Glue reader. -/
theorem lpnChal_eq (P : Params) (π : PrimeSchedule) (L : ℕ) : P.LPNChal π L =
    (Matrix (Fin ((P.lpnFamily_raw π).toLWE.parameters L).samples)
      (Fin ((P.lpnFamily_raw π).toLWE.parameters L).dimension)
      (ZMod ((P.lpnFamily_raw π).toLWE.parameters L).modulus) ×
    (Fin ((P.lpnFamily_raw π).toLWE.parameters L).samples →
      ZMod ((P.lpnFamily_raw π).toLWE.parameters L).modulus)) := rfl

/-- LPN encoding is exactly the assumption's `LWE.encodeChallenge`, with its own residue width
[JLS26, Lemma 4.2, p. 19]. Dv3 changes no assumption challenge or encoding. -/
noncomputable def lpnEnc (P : Params) (π : PrimeSchedule) (L : ℕ)
    (x : P.LPNChal π L) : List Bool :=
  LWE.encodeChallenge ((P.lpnFamily_raw π).toLWE.parameters L)
    ((P.lpnFamily_raw π).toLWE.residueBits.eval L) x

/-- The LPN encoding is the unchanged canonical family challenge code. Glue reader. -/
theorem lpnEnc_eq (P : Params) (π : PrimeSchedule) (L : ℕ) (x : P.LPNChal π L) :
    P.lpnEnc π L x = LWE.encodeChallenge ((P.lpnFamily_raw π).toLWE.parameters L)
      ((P.lpnFamily_raw π).toLWE.residueBits.eval L) x := rfl

/-- Canonical LPN secret dimension equals L. Glue composed from owner-side parameter readers. -/
theorem lpn_dimension_eq (P : Params) (π : PrimeSchedule) (L : ℕ) :
    ((P.lpnFamily_raw π).toLWE.parameters L).dimension = L :=
  (congrArg (fun Q : ℕ → LWE.Parameters => (Q L).dimension)
    (LPNFamily.Raw.toLWE_parameters (P.lpnFamily_raw π))).trans
      (LPNFamily.Raw.parameters_dimension (P.lpnFamily_raw π) L)

/-- Canonical LPN sample count equals L^D. Glue composed from owner-side parameter readers. -/
theorem lpn_samples_eq (P : Params) (π : PrimeSchedule) (L : ℕ) :
    ((P.lpnFamily_raw π).toLWE.parameters L).samples = L ^ P.D :=
  (congrArg (fun Q : ℕ → LWE.Parameters => (Q L).samples)
    (LPNFamily.Raw.toLWE_parameters (P.lpnFamily_raw π))).trans
      ((LPNFamily.Raw.parameters_samples (P.lpnFamily_raw π) L).trans
        (P.lpnFamily_raw_samples π L))

/-- Canonical LPN modulus is the prime at inverse dimension. Glue composed from owner readers. -/
theorem lpn_modulus_eq (P : Params) (π : PrimeSchedule) (L : ℕ) :
    ((P.lpnFamily_raw π).toLWE.parameters L).modulus = (π (P.kappaOf L)).p :=
  (congrArg (fun Q : ℕ → LWE.Parameters => (Q L).modulus)
    (LPNFamily.Raw.toLWE_parameters (P.lpnFamily_raw π))).trans
      ((LPNFamily.Raw.parameters_modulus (P.lpnFamily_raw π) L).trans
        (P.lpnFamily_raw_modulus π L))

/-- Concrete LPN coordinates expose rows L^D, columns L and the inverse-indexed prime
[JLS26, Lemma 4.2, p. 19]. Dv3 and Dv15 use only explicit transport from the assumption. -/
abbrev LPNConcrete (P : Params) (π : PrimeSchedule) (L : ℕ) : Type :=
  Matrix (Fin (L ^ P.D)) (Fin L) (ZMod (π (P.kappaOf L)).p) ×
    (Fin (L ^ P.D) → ZMod (π (P.kappaOf L)).p)

/-- Concrete LPN coordinates have the displayed finite matrix/value type. Glue reader. -/
theorem lpnConcrete_eq (P : Params) (π : PrimeSchedule) (L : ℕ) : P.LPNConcrete π L =
    (Matrix (Fin (L ^ P.D)) (Fin L) (ZMod (π (P.kappaOf L)).p) ×
      (Fin (L ^ P.D) → ZMod (π (P.kappaOf L)).p)) := rfl

/-- Canonical and concrete LPN challenges are related by explicit finite and residue casts
[JLS26, Lemma 4.2, p. 19]. Dv15 uses `finCongr` and `Equiv.cast`, with no chosen enumeration. -/
noncomputable def lpnChalEquiv (P : Params) (π : PrimeSchedule) (L : ℕ) :
    P.LPNChal π L ≃ P.LPNConcrete π L :=
  Equiv.prodCongr
    (Equiv.arrowCongr (finCongr (P.lpn_samples_eq π L))
      (Equiv.arrowCongr (finCongr (P.lpn_dimension_eq π L))
        (Equiv.cast (congrArg ZMod (P.lpn_modulus_eq π L)))))
    (Equiv.arrowCongr (finCongr (P.lpn_samples_eq π L))
      (Equiv.cast (congrArg ZMod (P.lpn_modulus_eq π L))))

/-- The challenge equivalence is its explicit product/arrow/finite-cast composition. Glue. -/
theorem lpnChalEquiv_eq (P : Params) (π : PrimeSchedule) (L : ℕ) :
    P.lpnChalEquiv π L = Equiv.prodCongr
      (Equiv.arrowCongr (finCongr (P.lpn_samples_eq π L))
        (Equiv.arrowCongr (finCongr (P.lpn_dimension_eq π L))
          (Equiv.cast (congrArg ZMod (P.lpn_modulus_eq π L)))))
      (Equiv.arrowCongr (finCongr (P.lpn_samples_eq π L))
        (Equiv.cast (congrArg ZMod (P.lpn_modulus_eq π L)))) := rfl

/-- Advice retains the hop, Boolean index, buckets, exact draw, Boolean tail and uniform vectors
[JLS26, Lemma 4.2, p. 19]. Dv12 hardwires averaged values rather than sampling; the extra
hop sentinel `Fin (κ+1)` keeps the type inhabited at every independent dimension L. -/
structure LPNAdvice (P : Params) (π : PrimeSchedule) (L : ℕ) where
  hop : Fin (P.kappaOf L + 1)
  I : P.G.Idx (P.n (P.kappaOf L))
  buckets : Fin (P.m (P.kappaOf L)) → Fin (P.B (P.kappaOf L))
  draw : P.Draw (P.kappaOf L) (π (P.kappaOf L))
  tail : Fin (P.m (P.kappaOf L)) → Bool
  uniform : Fin (P.kappaOf L) → Fin (P.n (P.kappaOf L)) → ZMod (π (P.kappaOf L)).p

/-- Advice has the explicit right-associated finite product of its six components. Glue. -/
abbrev LPNAdviceProduct (P : Params) (π : PrimeSchedule) (L : ℕ) : Type :=
  Fin (P.kappaOf L + 1) × (P.G.Idx (P.n (P.kappaOf L)) ×
    ((Fin (P.m (P.kappaOf L)) → Fin (P.B (P.kappaOf L))) ×
      (P.Draw (P.kappaOf L) (π (P.kappaOf L)) ×
        ((Fin (P.m (P.kappaOf L)) → Bool) ×
          (Fin (P.kappaOf L) → Fin (P.n (P.kappaOf L)) → ZMod (π (P.kappaOf L)).p)))))

/-- The advice product is the displayed right-associated tuple. Glue reader. -/
theorem lpnAdviceProduct_eq (P : Params) (π : PrimeSchedule) (L : ℕ) :
    P.LPNAdviceProduct π L =
      (Fin (P.kappaOf L + 1) × (P.G.Idx (P.n (P.kappaOf L)) ×
        ((Fin (P.m (P.kappaOf L)) → Fin (P.B (P.kappaOf L))) ×
          (P.Draw (P.kappaOf L) (π (P.kappaOf L)) ×
            ((Fin (P.m (P.kappaOf L)) → Bool) ×
              (Fin (P.kappaOf L) → Fin (P.n (P.kappaOf L)) →
                ZMod (π (P.kappaOf L)).p)))))) := rfl

/-- Advice records and their explicit component products are equivalent. Glue for Dv15. -/
def lpnAdviceProductEquiv (P : Params) (π : PrimeSchedule) (L : ℕ) :
    P.LPNAdvice π L ≃ P.LPNAdviceProduct π L where
  toFun w := (w.hop, w.I, w.buckets, w.draw, w.tail, w.uniform)
  invFun w := ⟨w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2.1, w.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Advice-product transport reads precisely the record's six fields. Glue reader. -/
theorem lpnAdviceProductEquiv_apply (P : Params) (π : PrimeSchedule) (L : ℕ)
    (w : P.LPNAdvice π L) :
    P.lpnAdviceProductEquiv π L w = (w.hop, w.I, w.buckets, w.draw, w.tail, w.uniform) := rfl

/-- Inverse advice-product transport constructs the record from its six coordinates. Glue reader. -/
theorem lpnAdviceProductEquiv_symm_apply (P : Params) (π : PrimeSchedule) (L : ℕ)
    (w : P.LPNAdviceProduct π L) :
    (P.lpnAdviceProductEquiv π L).symm w =
      ⟨w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2.1, w.2.2.2.2.2⟩ := rfl

/-- The explicit advice coordinate count is the product of its six finite cardinalities. Glue. -/
noncomputable def lpnAdviceCard (P : Params) (π : PrimeSchedule) (L : ℕ) : ℕ :=
  let κ := P.kappaOf L
  let pp := π κ
  (κ + 1) * (P.G.idxCard (P.n κ) * (P.B κ ^ P.m κ *
    (P.drawCard κ pp * (2 ^ P.m κ * ((pp.p ^ P.n κ) ^ κ)))))

/-- The advice coordinate count is the stated nested product. Glue reader. -/
theorem lpnAdviceCard_eq (P : Params) (π : PrimeSchedule) (L : ℕ) :
    P.lpnAdviceCard π L =
      let κ := P.kappaOf L
      let pp := π κ
      (κ + 1) * (P.G.idxCard (P.n κ) * (P.B κ ^ P.m κ *
        (P.drawCard κ pp * (2 ^ P.m κ * ((pp.p ^ P.n κ) ^ κ))))) := rfl

/-- Advice has explicit Fin coordinates assembled from its supplied and canonical equivalences
[JLS26, Lemma 4.2, p. 19]. Dv15 uses no classical finite enumeration. -/
noncomputable def lpnAdviceEquiv (P : Params) (π : PrimeSchedule) (L : ℕ) :
    P.LPNAdvice π L ≃ Fin (P.lpnAdviceCard π L) :=
  let κ := P.kappaOf L
  let pp := π κ
  let eTail := (Equiv.prodCongr (ConstructionEncoding.boolVectorEquiv (P.m κ))
    ((Equiv.arrowCongr (Equiv.refl (Fin κ))
      (ConstructionEncoding.vectorEquiv pp (P.n κ))).trans finFunctionFinEquiv)).trans
        finProdFinEquiv
  let eDraw := (Equiv.prodCongr (P.drawEquiv κ pp) eTail).trans finProdFinEquiv
  let eBuckets := (Equiv.prodCongr finFunctionFinEquiv eDraw).trans finProdFinEquiv
  let eIndex := (Equiv.prodCongr (P.G.idxEquiv (P.n κ)) eBuckets).trans finProdFinEquiv
  (P.lpnAdviceProductEquiv π L).trans
    ((Equiv.prodCongr (Equiv.refl (Fin (κ + 1))) eIndex).trans finProdFinEquiv)

/-- Advice Fin coordinates use the displayed tail/draw/bucket/index product composition. Glue. -/
theorem lpnAdviceEquiv_eq (P : Params) (π : PrimeSchedule) (L : ℕ) :
    P.lpnAdviceEquiv π L =
      let κ := P.kappaOf L
      let pp := π κ
      let eTail := (Equiv.prodCongr (ConstructionEncoding.boolVectorEquiv (P.m κ))
        ((Equiv.arrowCongr (Equiv.refl (Fin κ))
          (ConstructionEncoding.vectorEquiv pp (P.n κ))).trans finFunctionFinEquiv)).trans
            finProdFinEquiv
      let eDraw := (Equiv.prodCongr (P.drawEquiv κ pp) eTail).trans finProdFinEquiv
      let eBuckets := (Equiv.prodCongr finFunctionFinEquiv eDraw).trans finProdFinEquiv
      let eIndex := (Equiv.prodCongr (P.G.idxEquiv (P.n κ)) eBuckets).trans finProdFinEquiv
      (P.lpnAdviceProductEquiv π L).trans
        ((Equiv.prodCongr (Equiv.refl (Fin (κ + 1))) eIndex).trans finProdFinEquiv) := rfl

noncomputable instance instLPNAdviceFintype (P : Params) (π : PrimeSchedule) (L : ℕ) :
    Fintype (P.LPNAdvice π L) :=
  Fintype.ofEquiv (Fin (P.lpnAdviceCard π L)) (P.lpnAdviceEquiv π L).symm

/-- The LPN advice finiteness instance is induced by its explicit Fin equivalence; glue. -/
theorem instLPNAdviceFintype_eq (P : Params) (π : PrimeSchedule) (L : ℕ) :
    instLPNAdviceFintype P π L =
      Fintype.ofEquiv (Fin (P.lpnAdviceCard π L)) (P.lpnAdviceEquiv π L).symm := rfl

instance instLPNAdviceNonempty (P : Params) (π : PrimeSchedule) (L : ℕ) :
    Nonempty (P.LPNAdvice π L) :=
  Nonempty.map (P.lpnAdviceProductEquiv π L).symm
    (inferInstanceAs (Nonempty (P.LPNAdviceProduct π L)))

/-- Advice encoding begins with the prime and unary L, followed by its six explicit components
[JLS26, Lemma 4.2, p. 19]. Dv9, Dv12 and Dv15 give the preprocessor all parameters as input;
the hardwired tail avoids calling the PRG. No sampler or choice-based code occurs here. -/
noncomputable def encLPNAdvice (P : Params) (π : PrimeSchedule) (L : ℕ)
    (w : P.LPNAdvice π L) : List Bool :=
  let κ := P.kappaOf L
  let pp := π κ
  pairEncode pp.enc (pairEncode (List.replicate L true)
    (pairEncode (Candidates.natToList (κ + 1) w.hop.val)
      (pairEncode (P.G.encIdx (P.n κ) w.I)
        (pairEncode (P.encBuckets κ w.buckets)
          (pairEncode (P.encDraw κ pp w.draw)
            (pairEncode (List.ofFn w.tail)
              (BoolCircuit.encodeList (Encoding.Modular.encodeVector (κ + 1))
                (List.ofFn w.uniform))))))))

/-- Advice encoding is the displayed prime-first nested pair of all six fields. Glue reader. -/
theorem encLPNAdvice_eq (P : Params) (π : PrimeSchedule) (L : ℕ)
    (w : P.LPNAdvice π L) : P.encLPNAdvice π L w =
      let κ := P.kappaOf L
      let pp := π κ
      pairEncode pp.enc (pairEncode (List.replicate L true)
        (pairEncode (Candidates.natToList (κ + 1) w.hop.val)
          (pairEncode (P.G.encIdx (P.n κ) w.I)
            (pairEncode (P.encBuckets κ w.buckets)
              (pairEncode (P.encDraw κ pp w.draw)
                (pairEncode (List.ofFn w.tail)
                  (BoolCircuit.encodeList (Encoding.Modular.encodeVector (κ + 1))
                    (List.ofFn w.uniform)))))))) := rfl

/-- A syntactic bound for all encoded LPN advice is `4096*(L+1)*S(L)^3`, where S sums
index, seed, output, Boolean-seed and secret bounds and L+1. Glue for Dv12 and Dv15.
The generous constant bounds all nested separators without an asymptotic hidden factor. -/
def lpnAdviceBound (P : Params) : PolyExpr :=
  .mul (.const 4096) (.mul (.add .var (.const 1))
    (.pow (.add P.idxBound (.add P.seedBound (.add P.mBound
      (.add P.nBound (.add P.ellBound (.add .var (.const 1))))))) 3))

/-- The LPN advice bound is its displayed syntactic polynomial. Glue reader. -/
theorem lpnAdviceBound_eq (P : Params) : P.lpnAdviceBound =
    .mul (.const 4096) (.mul (.add .var (.const 1))
      (.pow (.add P.idxBound (.add P.seedBound (.add P.mBound
        (.add P.nBound (.add P.ellBound (.add .var (.const 1))))))) 3)) := rfl

/-- On a scheduled dimension, the challenged matrix is transported to the exact κ dimensions
[JLS26, Lemma 4.2, p. 19]. Dv15 uses only `finCongr` and published length equations. -/
noncomputable def lpnMatrixAt (P : Params) (π : PrimeSchedule) (L : ℕ)
    (h : L = P.ℓ (P.kappaOf L)) (x : P.LPNChal π L) :
    Matrix (Fin (P.n (P.kappaOf L))) (Fin (P.ℓ (P.kappaOf L)))
      (ZMod (π (P.kappaOf L)).p) :=
  fun i a => (P.lpnChalEquiv π L x).1
    ((finCongr ((congrArg (fun q : ℕ => q ^ P.D) h).trans
      (P.n_eq (P.kappaOf L)).symm)).symm i) ((finCongr h).symm a)

/-- The matrix transport is the displayed explicit row/column finite cast. Glue reader. -/
theorem lpnMatrixAt_eq (P : Params) (π : PrimeSchedule) (L : ℕ)
    (h : L = P.ℓ (P.kappaOf L)) (x : P.LPNChal π L) :
    P.lpnMatrixAt π L h x = fun i a => (P.lpnChalEquiv π L x).1
      ((finCongr ((congrArg (fun q : ℕ => q ^ P.D) h).trans
        (P.n_eq (P.kappaOf L)).symm)).symm i) ((finCongr h).symm a) := rfl

/-- On a scheduled dimension, challenged values use the corresponding explicit row transport
[JLS26, Lemma 4.2, p. 19]. Dv15 changes no challenge coordinate. -/
noncomputable def lpnValuesAt (P : Params) (π : PrimeSchedule) (L : ℕ)
    (h : L = P.ℓ (P.kappaOf L)) (x : P.LPNChal π L) :
    Fin (P.n (P.kappaOf L)) → ZMod (π (P.kappaOf L)).p :=
  fun i => (P.lpnChalEquiv π L x).2
    ((finCongr ((congrArg (fun q : ℕ => q ^ P.D) h).trans
      (P.n_eq (P.kappaOf L)).symm)).symm i)

/-- Value transport is the displayed row cast of the concrete challenge. Glue reader. -/
theorem lpnValuesAt_eq (P : Params) (π : PrimeSchedule) (L : ℕ)
    (h : L = P.ℓ (P.kappaOf L)) (x : P.LPNChal π L) :
    P.lpnValuesAt π L h x = fun i => (P.lpnChalEquiv π L x).2
      ((finCongr ((congrArg (fun q : ℕ => q ^ P.D) h).trans
        (P.n_eq (P.kappaOf L)).symm)).symm i) := rfl

/-- LPN preprocessing replaces the chosen instance by challenged values plus σ, leaves earlier
instances uniform and later instances real, and publishes the hardwired tail with error zero
[JLS26, Lemma 4.2, p. 19]. Dv12 uses only advice and the challenge; it neither samples nor
calls PRG evaluation. Off the schedule image it returns the empty word. -/
noncomputable def lpnPre (P : Params) (π : PrimeSchedule) (L : ℕ)
    (w : P.LPNAdvice π L) (x : P.LPNChal π L) : List Bool :=
  let κ := P.kappaOf L
  let pp := π κ
  if h : L = P.ℓ κ then
    let A := P.lpnMatrixAt π L h x
    let b := P.lpnValuesAt π L h x
    let I : P.Idx' κ pp := (w.I, w.buckets, A)
    let bs := fun k : Fin κ => if k.val < w.hop.val then w.uniform k else
      if k.val = w.hop.val then fun i => b i + ((w.draw.1 i).toNat : ZMod pp.p)
      else P.lpnVector κ pp A w.draw.1 (w.draw.2 k).1 (w.draw.2 k).2
    P.challengeStr κ pp I (P.publicSeed κ pp bs false) w.tail
  else []

/-- LPN preprocessing is its guarded, deterministic hybrid challenge construction. Glue reader. -/
theorem lpnPre_eq (P : Params) (π : PrimeSchedule) (L : ℕ)
    (w : P.LPNAdvice π L) (x : P.LPNChal π L) : P.lpnPre π L w x =
      let κ := P.kappaOf L
      let pp := π κ
      if h : L = P.ℓ κ then
        let A := P.lpnMatrixAt π L h x
        let b := P.lpnValuesAt π L h x
        let I : P.Idx' κ pp := (w.I, w.buckets, A)
        let bs := fun k : Fin κ => if k.val < w.hop.val then w.uniform k else
          if k.val = w.hop.val then fun i => b i + ((w.draw.1 i).toNat : ZMod pp.p)
          else P.lpnVector κ pp A w.draw.1 (w.draw.2 k).1 (w.draw.2 k).2
        P.challengeStr κ pp I (P.publicSeed κ pp bs false) w.tail
      else [] := rfl

/-- The explicit LPN reduction invokes A at κOf(L) with preprocessing and a coin prefix
[JLS26, Lemma 4.2, p. 19]. Dv12 and Dv14 separate its typed function from its machine;
advice is an input and no machine or sampler is constructed. -/
noncomputable def lpnRed (P : Params) (π : PrimeSchedule) (A : NUPPT) (L : ℕ)
    (w : P.LPNAdvice π L) (x : P.LPNChal π L) (r : List Bool) : List Bool :=
  A.runAtL (P.kappaOf L) (P.lpnPre π L w x) (r.take (A.coinLen (P.kappaOf L)))

/-- The reduction calls A on its preprocessed challenge and the stated prefix. Glue reader. -/
theorem lpnRed_eq (P : Params) (π : PrimeSchedule) (A : NUPPT) (L : ℕ)
    (w : P.LPNAdvice π L) (x : P.LPNChal π L) (r : List Bool) :
    P.lpnRed π A L w x r =
      A.runAtL (P.kappaOf L) (P.lpnPre π L w x) (r.take (A.coinLen (P.kappaOf L))) := rfl

/-- Canonical LPN challenge encoding is injective [JLS26, Lemma 4.2, p. 19].
Dv3 reuses the assumption's width and canonical encoder unchanged.

**Proof sketch.** Apply the existing `LWE.encodeChallenge_injective` with the LWE
family's public modulus-width field. -/
theorem lpnEnc_injective (P : Params) (π : PrimeSchedule) (L : ℕ) :
    Function.Injective (P.lpnEnc π L) := sorry

/-- All six hardwired advice fields are retained by the explicit code
[JLS26, Lemma 4.2, p. 19]. Dv9 and Dv15 place the prime first and use fixed coordinate codes.

**Proof sketch.** Split the nested pairs, recover hop/index/bucket/draw/tail coordinates,
and use modular vector injectivity on each uniform-vector list entry. -/
theorem encLPNAdvice_injective (P : Params) (π : PrimeSchedule) (L : ℕ) :
    Function.Injective (P.encLPNAdvice π L) := sorry

/-- Every advice word has length at most the explicit polynomial at its independent dimension
[JLS26, Lemma 4.2, p. 19]. Dv12 and Dv15 count hardwired data rather than sampler coins.

**Proof sketch.** Use the existing pair/list/vector length equations, the exact draw
layout, the published numeric bounds, κOf(L)≤L and PolyExpr.eval_mono; the factor4096
covers all separators in the deliberately generous cubic majorant. -/
theorem encLPNAdvice_length_le (P : Params) (π : PrimeSchedule) (L : ℕ)
    (w : P.LPNAdvice π L) : (P.encLPNAdvice π L w).length ≤ P.lpnAdviceBound.eval L := sorry

/-- One advice family bounds any selected LPN hop for every realizing non-uniform PPT machine
[JLS26, Lemma 4.2, p. 19]. Dv8 and Dv12 retain buckets and hardwire averaged values.
Dv16 uses the shared, layout-length-only RealizesOn; more realisers are admitted, so this
security statement is at least as strong as the every-coin-string draft. The sentinel
hop makes advice inhabited at κ=0; the hop inequality is requested only below κ.

**Proof sketch.** For each scheduled dimension, average over every nonchallenge value
and fix a maximizing advice tuple. Reindex at ℓ(κ), transport the canonical challenge
by its explicit equivalence, and use the shared realiser verdict/coin readers. Uniform
coin prefixes recover A's coins; the resulting gap is bounded by the LPN advantage. -/
theorem lpn_hop (P : Params) (π : PrimeSchedule) (A : NUPPT)
    (tails : ℕ → Bool) (hops : ∀ κ, Fin (κ + 1)) :
    ∃ w : ∀ L, P.LPNAdvice π L, ∀ B : NUPPT,
      B.RealizesOn (P.lpnEnc π) (A.coins.subst .var)
        (fun L x r => P.lpnRed π A L (w L) x r) →
      ∀ κ, (hops κ).val < κ →
        Games.advantage (P.chainGame A (tails κ) (hops κ).val κ (π κ))
          (P.chainGame A (tails κ) ((hops κ).val + 1) κ (π κ)) ≤
            (P.lpnFamily_raw π).adv B (P.ℓ κ) := sorry

/-- LPN realizability says every adversary and every polynomially bounded typed advice family
has a machine realizing the explicit reduction. [JLS26, Lemma 4.2, p. 19]. Dv14 leaves this
as the named Phase B obligation; the target link supplies it without constructing machines
here. Dv16 uses shared RealizesOn on encoded challenges and layout-length coins only,
which admits more realisers and makes this proposition easier than its every-string draft. -/
def LPNRealizable (P : Params) (π : PrimeSchedule) : Prop :=
  ∀ (A : NUPPT) (w : ∀ L, P.LPNAdvice π L), ∃ B : NUPPT,
    B.RealizesOn (P.lpnEnc π) (A.coins.subst .var)
      (fun L x r => P.lpnRed π A L (w L) x r)

/-- LPN realizability is the explicit contract for every adversary and advice family.
Glue reader. -/
theorem LPNRealizable_iff (P : Params) (π : PrimeSchedule) :
    P.LPNRealizable π ↔
      ∀ (A : NUPPT) (w : ∀ L, P.LPNAdvice π L), ∃ B : NUPPT,
        B.RealizesOn (P.lpnEnc π) (A.coins.subst .var)
          (fun L x r => P.lpnRed π A L (w L) x r) := Iff.rfl

end Params

end TCSlib.Cryptography.Obfuscation.StructuredSeed
