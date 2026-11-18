/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Hybrids
import TCSlib.Cryptography.Asymptotic.Realization

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The explicit advice-taking JLS Boolean PRG reduction

## Main definitions

* `Params.PRGChal`, `Params.prgEnc`: the canonical Boolean assumption challenge.
* `Params.PRGAdvice`, `Params.prgAdviceEquiv`: inhabited explicit finite advice.
* `Params.encPRGAdvice`, `Params.prgAdviceBound`: the faithful public-prime-first advice code.
* `Params.prgPre`, `Params.prgRed`: deterministic preprocessing and the explicit reduction.
* `Params.PRGRealizable`: the shared encoded-challenge realisation obligation.

## Main results

* `Params.encPRGAdvice_length_le` is the explicit polynomial advice bound.
* `Params.prg_hop` bounds the all-uniform-public-vector hop for every realiser.
* Every definition has a proved owner-side reader.

## References

* [JLS26] A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Well-Founded Assumptions*, J. ACM 73(1), Article 1, February 2026,
  Lemma 4.2 and its proof, p. 19.

Dv8 retains the independent bucket map in the challenge. Dv9 reads the public prime
from advice. Dv12 hardwires averaged-out values instead of sampling them in the
reduction. Dv14 separates the function from its Phase B machine realisability target;
Dv15 fixes explicit finite coordinates, and Dv16 uses the shared layout-length
RealizesOn contract. This module constructs neither a machine nor a sampler.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
  3rd ed., January 2010, Definition 26.8 (non-uniform PPT adversaries).
-/

namespace TCSlib.Cryptography.Obfuscation.StructuredSeed

open Complexity Turing Games

namespace Params

/-- The Boolean assumption challenge is an index and a Boolean output vector:
`PRGChal N = G.Idx N × (Fin (G.outLen N) → Bool)`.
[JLS26, Lemma 4.2, p. 19]. Dv4 indexes the Boolean assumption by its own seed length. -/
abbrev PRGChal (P : Params) (N : ℕ) : Type :=
  P.G.Idx N × (Fin (P.G.outLen N) → Bool)

/-- The Boolean challenge type is the stated index/output pair; glue. -/
theorem prgChal_eq (P : Params) (N : ℕ) :
    P.PRGChal N = (P.G.Idx N × (Fin (P.G.outLen N) → Bool)) := rfl

/-- The explicit Boolean challenge size is `G.idxCard N * 2^(G.outLen N)`; glue. -/
def prgChalCard (P : Params) (N : ℕ) : ℕ := P.G.idxCard N * 2 ^ P.G.outLen N

/-- The challenge size is the displayed index/vector product; glue. -/
theorem prgChalCard_eq (P : Params) (N : ℕ) :
    P.prgChalCard N = P.G.idxCard N * 2 ^ P.G.outLen N := rfl

/-- The Boolean challenge has explicit finite coordinates from the supplied index
coordinates and canonical Boolean vector equivalence; glue. -/
def prgChalEquiv (P : Params) (N : ℕ) : P.PRGChal N ≃ Fin (P.prgChalCard N) :=
  (Equiv.prodCongr (P.G.idxEquiv N)
    (ConstructionEncoding.boolVectorEquiv (P.G.outLen N))).trans finProdFinEquiv

/-- The challenge equivalence is the displayed index/vector/product composition; glue. -/
theorem prgChalEquiv_eq (P : Params) (N : ℕ) :
    P.prgChalEquiv N =
      (Equiv.prodCongr (P.G.idxEquiv N)
        (ConstructionEncoding.boolVectorEquiv (P.G.outLen N))).trans finProdFinEquiv := rfl

/-- The encoded assumption challenge is exactly the Boolean primitive's canonical challenge,
`prgEnc N x = G.challengeStr N x.1 x.2`. [JLS26, Lemma 4.2, p. 19]. The Boolean
assumption has no modulus field; the construction prime is carried in reduction advice. -/
def prgEnc (P : Params) (N : ℕ) (x : P.PRGChal N) : List Bool :=
  P.G.challengeStr N x.1 x.2

/-- The assumption encoding is the canonical index/output challenge; glue. -/
theorem prgEnc_eq (P : Params) (N : ℕ) (x : P.PRGChal N) :
    P.prgEnc N x = P.G.challengeStr N x.1 x.2 := rfl

/-- PRG-hop advice fixes the bucket map, LPN matrix and all uniform public vectors at
`kappa = kappaOfN N`. [JLS26, Lemma 4.2, p. 19]. Dv12 hardwires exactly the values
averaged out by the paper's final Boolean PRG hop; Dv9 supplies any prime schedule. -/
structure PRGAdvice (P : Params) (π : PrimeSchedule) (N : ℕ) where
  /-- The fixed bucket placement. -/
  buckets : Fin (P.m (P.kappaOfN N)) → Fin (P.B (P.kappaOfN N))
  /-- The fixed public LPN matrix. -/
  matrix : Matrix (Fin (P.n (P.kappaOfN N))) (Fin (P.ℓ (P.kappaOfN N)))
    (ZMod (π (P.kappaOfN N)).p)
  /-- The fixed independent uniform public vectors. -/
  uniform : Fin (P.kappaOfN N) → Fin (P.n (P.kappaOfN N)) →
    ZMod (π (P.kappaOfN N)).p

namespace PRGAdvice

/-- The advice data is the bucket/matrix/uniform-vector product; glue. -/
abbrev Data (P : Params) (π : PrimeSchedule) (N : ℕ) : Type :=
  (Fin (P.m (P.kappaOfN N)) → Fin (P.B (P.kappaOfN N))) ×
    (Matrix (Fin (P.n (P.kappaOfN N))) (Fin (P.ℓ (P.kappaOfN N)))
        (ZMod (π (P.kappaOfN N)).p) ×
      (Fin (P.kappaOfN N) → Fin (P.n (P.kappaOfN N)) →
        ZMod (π (P.kappaOfN N)).p))

/-- The advice-data type is the displayed product; glue. -/
theorem data_eq (P : Params) (π : PrimeSchedule) (N : ℕ) : Data P π N =
    ((Fin (P.m (P.kappaOfN N)) → Fin (P.B (P.kappaOfN N))) ×
      (Matrix (Fin (P.n (P.kappaOfN N))) (Fin (P.ℓ (P.kappaOfN N)))
          (ZMod (π (P.kappaOfN N)).p) ×
        (Fin (P.kappaOfN N) → Fin (P.n (P.kappaOfN N)) →
          ZMod (π (P.kappaOfN N)).p))) := rfl

/-- The advice record is identified explicitly with its product of fields; glue.
The inverse is the record constructor, with both inverse laws given by record reduction. -/
def prodEquiv (P : Params) (π : PrimeSchedule) (N : ℕ) :
    P.PRGAdvice π N ≃ Data P π N where
  toFun ω := (ω.buckets, ω.matrix, ω.uniform)
  invFun x := ⟨x.1, x.2.1, x.2.2⟩
  left_inv := fun ⟨_, _, _⟩ => rfl
  right_inv := fun ⟨_, _, _⟩ => rfl

/-- The record/product equivalence has the stated projections and constructor; glue. -/
theorem prodEquiv_eq (P : Params) (π : PrimeSchedule) (N : ℕ) :
    prodEquiv P π N =
      { toFun := fun ω => (ω.buckets, ω.matrix, ω.uniform)
        invFun := fun x => ⟨x.1, x.2.1, x.2.2⟩
        left_inv := fun ⟨_, _, _⟩ => rfl
        right_inv := fun ⟨_, _, _⟩ => rfl } := rfl

end PRGAdvice

/-- The explicit advice size is `B^m * ((p^ell)^n * (p^n)^kappa)`; glue.
Every parameter is read at kappaOfN N and no enumeration is chosen. -/
noncomputable def prgAdviceCard (P : Params) (π : PrimeSchedule) (N : ℕ) : ℕ :=
  P.B (P.kappaOfN N) ^ P.m (P.kappaOfN N) *
    (((π (P.kappaOfN N)).p ^ P.ℓ (P.kappaOfN N)) ^ P.n (P.kappaOfN N) *
      (((π (P.kappaOfN N)).p ^ P.n (P.kappaOfN N)) ^ P.kappaOfN N))

/-- The advice size is the displayed bucket/matrix/uniform-vector product; glue. -/
theorem prgAdviceCard_eq (P : Params) (π : PrimeSchedule) (N : ℕ) :
    P.prgAdviceCard π N = P.B (P.kappaOfN N) ^ P.m (P.kappaOfN N) *
      (((π (P.kappaOfN N)).p ^ P.ℓ (P.kappaOfN N)) ^ P.n (P.kappaOfN N) *
        (((π (P.kappaOfN N)).p ^ P.n (P.kappaOfN N)) ^ P.kappaOfN N)) := rfl

/-- Advice has explicit Fin coordinates from the record/product equivalence and canonical
function/matrix/product coordinates. [JLS26, Lemma 4.2, p. 19]. Dv15 forbids any chosen
finite enumeration; Dv12's averaged-out data is represented in full. -/
noncomputable def prgAdviceEquiv (P : Params) (π : PrimeSchedule) (N : ℕ) :
    P.PRGAdvice π N ≃ Fin (P.prgAdviceCard π N) :=
  (PRGAdvice.prodEquiv P π N).trans
    ((Equiv.prodCongr finFunctionFinEquiv
      ((Equiv.prodCongr
        (ConstructionEncoding.matrixEquiv (π (P.kappaOfN N))
          (P.n (P.kappaOfN N)) (P.ℓ (P.kappaOfN N)))
        (ConstructionEncoding.matrixEquiv (π (P.kappaOfN N))
          (P.kappaOfN N) (P.n (P.kappaOfN N)))).trans finProdFinEquiv)).trans
      finProdFinEquiv)

/-- The advice equivalence is the displayed record/function/matrix/product composition; glue. -/
theorem prgAdviceEquiv_eq (P : Params) (π : PrimeSchedule) (N : ℕ) :
    P.prgAdviceEquiv π N = (PRGAdvice.prodEquiv P π N).trans
      ((Equiv.prodCongr finFunctionFinEquiv
        ((Equiv.prodCongr
          (ConstructionEncoding.matrixEquiv (π (P.kappaOfN N))
            (P.n (P.kappaOfN N)) (P.ℓ (P.kappaOfN N)))
          (ConstructionEncoding.matrixEquiv (π (P.kappaOfN N))
            (P.kappaOfN N) (P.n (P.kappaOfN N)))).trans finProdFinEquiv)).trans
        finProdFinEquiv) := rfl

noncomputable instance instPRGAdviceFintype (P : Params) (π : PrimeSchedule) (N : ℕ) :
    Fintype (P.PRGAdvice π N) :=
  Fintype.ofEquiv (Fin (P.prgAdviceCard π N)) (P.prgAdviceEquiv π N).symm

/-- The PRG advice finiteness instance is induced by its explicit Fin equivalence; glue. -/
theorem instPRGAdviceFintype_eq (P : Params) (π : PrimeSchedule) (N : ℕ) :
    instPRGAdviceFintype P π N =
      Fintype.ofEquiv (Fin (P.prgAdviceCard π N)) (P.prgAdviceEquiv π N).symm := rfl

noncomputable instance instPRGAdviceInhabited (P : Params) (π : PrimeSchedule) (N : ℕ) :
    Inhabited (P.PRGAdvice π N) where
  default :=
    { buckets := fun _ => ⟨0, P.B_pos (P.kappaOfN N)⟩
      matrix := fun _ _ => 0
      uniform := fun _ _ => 0 }

/-- The PRG advice default is the explicit zero bucket placement, matrix and vectors; glue. -/
theorem instPRGAdviceInhabited_eq (P : Params) (π : PrimeSchedule) (N : ℕ) :
    instPRGAdviceInhabited P π N =
      { default :=
          { buckets := fun _ => ⟨0, P.B_pos (P.kappaOfN N)⟩
            matrix := fun _ _ => 0
            uniform := fun _ _ => 0 } } := rfl

/-- The advice word starts with the public prime, followed by unary N, bucket placement,
the LPN matrix, and the uniform vectors encoded as a kappa-by-n matrix.
[JLS26, Lemma 4.2, p. 19]. Dv9 publishes the prime as input; Dv12 and Dv15 encode every
hardwired value in explicit finite coordinates. The code never computes a prime. -/
noncomputable def encPRGAdvice (P : Params) (π : PrimeSchedule) (N : ℕ)
    (ω : P.PRGAdvice π N) : List Bool :=
  pairEncode (π (P.kappaOfN N)).enc
    (pairEncode (List.replicate N true)
      (pairEncode (P.encBuckets (P.kappaOfN N) ω.buckets)
        (pairEncode (Encoding.Modular.encodeMatrix (P.kappaOfN N + 1) ω.matrix)
          (Encoding.Modular.encodeMatrix (P.kappaOfN N + 1) ω.uniform))))

/-- The advice code is the stated public-prime-first nested pair; glue. -/
theorem encPRGAdvice_eq (P : Params) (π : PrimeSchedule) (N : ℕ)
    (ω : P.PRGAdvice π N) :
    P.encPRGAdvice π N ω = pairEncode (π (P.kappaOfN N)).enc
      (pairEncode (List.replicate N true)
        (pairEncode (P.encBuckets (P.kappaOfN N) ω.buckets)
          (pairEncode (Encoding.Modular.encodeMatrix (P.kappaOfN N + 1) ω.matrix)
            (Encoding.Modular.encodeMatrix (P.kappaOfN N + 1) ω.uniform)))) := rfl

/-- The advice-data majorant is the sum of the index, seed, output, Boolean-seed, LPN-dimension,
and unary-parameter bounds, plus one; glue. -/
def prgAdviceDataBound (P : Params) : PolyExpr :=
  .add P.idxBound (.add P.seedBound (.add P.mBound
    (.add P.nBound (.add P.ellBound (.add .var (.const 1))))))

/-- The advice-data majorant is its explicit polynomial sum; glue. -/
theorem prgAdviceDataBound_eq (P : Params) : P.prgAdviceDataBound =
    .add P.idxBound (.add P.seedBound (.add P.mBound
      (.add P.nBound (.add P.ellBound (.add .var (.const 1)))))) := rfl

/-- The explicit advice bound is `100*(N+1)*(dataBound(N))^3`; glue.
The coarse majorant covers every pairing separator, public-prime bit and fixed-width entry. -/
def prgAdviceBound (P : Params) : PolyExpr :=
  .mul (.const 100) (.mul (.add .var (.const 1)) (.pow P.prgAdviceDataBound 3))

/-- The advice bound is the displayed cubic polynomial; glue. -/
theorem prgAdviceBound_eq (P : Params) : P.prgAdviceBound =
    .mul (.const 100) (.mul (.add .var (.const 1)) (.pow P.prgAdviceDataBound 3)) := rfl

/-- Preprocessing checks the Boolean schedule image, casts the supplied assumption index
and output, and publishes the fixed uniform public vectors with error flag false.
[JLS26, Lemma 4.2, p. 19]. Dv9 and Dv12 read the prime and all fixed data from advice;
Dv14 and Dv15 leave machine implementation to its named target. Off-image inputs return
an empty word. Neither the generator evaluator nor any sampling operation is called. -/
noncomputable def prgPre (P : Params) (π : PrimeSchedule) (N : ℕ)
    (ω : P.PRGAdvice π N) (x : P.PRGChal N) : List Bool :=
  let κ := P.kappaOfN N
  if h : N = P.n κ then
    P.challengeStr κ (π κ) (cast (congrArg P.G.Idx h) x.1, ω.buckets, ω.matrix)
      (P.publicSeed κ (π κ) ω.uniform false)
      (fun j => x.2 ((finCongr (congrArg P.G.outLen h)).symm (P.outputIndex κ j)))
  else []

/-- The preprocessing map has the stated schedule guard, explicit transports and layout; glue. -/
theorem prgPre_eq (P : Params) (π : PrimeSchedule) (N : ℕ)
    (ω : P.PRGAdvice π N) (x : P.PRGChal N) :
    P.prgPre π N ω x =
      let κ := P.kappaOfN N
      if h : N = P.n κ then
        P.challengeStr κ (π κ) (cast (congrArg P.G.Idx h) x.1, ω.buckets, ω.matrix)
          (P.publicSeed κ (π κ) ω.uniform false)
          (fun j => x.2 ((finCongr (congrArg P.G.outLen h)).symm (P.outputIndex κ j)))
      else [] := rfl

/-- The explicit reduction runs A at kappaOfN N on the deterministic preprocessing and the
required coin prefix. [JLS26, Lemma 4.2, p. 19]. Dv12 hardwires the averaged data;
Dv14 supplies no machine and assumes no uniform sampling of extra reduction coins. -/
noncomputable def prgRed (P : Params) (π : PrimeSchedule) (A : NUPPT) (N : ℕ)
    (ω : P.PRGAdvice π N) (x : P.PRGChal N) (r : List Bool) : List Bool :=
  A.runAtL (P.kappaOfN N) (P.prgPre π N ω x)
    (r.take (A.coinLen (P.kappaOfN N)))

/-- The reduction is exactly runAtL at the inverse parameter with the stated prefix; glue. -/
theorem prgRed_eq (P : Params) (π : PrimeSchedule) (A : NUPPT) (N : ℕ)
    (ω : P.PRGAdvice π N) (x : P.PRGChal N) (r : List Bool) :
    P.prgRed π A N ω x r = A.runAtL (P.kappaOfN N) (P.prgPre π N ω x)
      (r.take (A.coinLen (P.kappaOfN N))) := rfl

/-- Boolean reduction realisability requires a shared-contract realiser for every adversary
and every advice family. [JLS26, Lemma 4.2, p. 19]. Dv14 leaves this as a Phase B
obligation, linked to preprocessing targets later. Dv16: the shared RealizesOn constrains
only encoded challenges and coin strings of layout length; consequently every-realiser
security is at least as strong as with the earlier all-coin-strings form.
Phase B obligation; not proved in this development. -/
def PRGRealizable (P : Params) (π : PrimeSchedule) : Prop :=
  ∀ (A : NUPPT) (ω : ∀ N, P.PRGAdvice π N), ∃ B : NUPPT,
    B.RealizesOn P.prgEnc (A.coins.subst .var)
      (fun N x r => P.prgRed π A N (ω N) x r)

/-- Boolean realisability is the explicit shared encoded-challenge contract; glue. -/
theorem PRGRealizable_iff (P : Params) (π : PrimeSchedule) :
    P.PRGRealizable π ↔ ∀ (A : NUPPT) (ω : ∀ N, P.PRGAdvice π N), ∃ B : NUPPT,
      B.RealizesOn P.prgEnc (A.coins.subst .var)
        (fun N x r => P.prgRed π A N (ω N) x r) := Iff.rfl

/-- The canonical Boolean challenge encoding is injective.
[JLS26, Definition 3.4, p. 11; Lemma 4.2, p. 19]. Dv15 retains the complete typed challenge.

**Proof sketch.** Read the canonical challenge pair through prgEnc_eq and challengeStr_eq,
then apply the primitive's index-code injectivity and List.ofFn injectivity. -/
theorem prgEnc_injective (P : Params) (N : ℕ) : Function.Injective (P.prgEnc N) := sorry

/-- The explicit PRG-hop advice code retains every fixed bucket, matrix and public vector.
[JLS26, Lemma 4.2, p. 19]. Dv9, Dv12 and Dv15 retain the prime prefix and all hardwired data.

**Proof sketch.** Split the nested pairs, apply the bucket-code and canonical matrix-code
injectivity readers at the public prime's residue width, then use record extensionality. -/
theorem encPRGAdvice_injective (P : Params) (π : PrimeSchedule) (N : ℕ) :
    Function.Injective (P.encPRGAdvice π N) := sorry

/-- Every advice encoding fits the explicit syntactic polynomial at N.
[JLS26, Lemma 4.2, p. 19]. Dv12 bounds the full hardwired data instead of using fresh
sampling; Dv15 accounts for its concrete finite-coordinate string.

**Proof sketch.** Read the nested pair lengths and canonical matrix lengths. Bound buckets
and the LPN matrix by idxBound, and the repeated uniform vectors by the public seed bound
with residue width kappa+1. Apply kappaOfN_le and polynomial evaluation monotonicity, then
absorb all constant and linear factors into the stated cubic majorant. -/
theorem encPRGAdvice_length_le (P : Params) (π : PrimeSchedule) (N : ℕ)
    (ω : P.PRGAdvice π N) :
    (P.encPRGAdvice π N ω).length ≤ P.prgAdviceBound.eval N := sorry

/-- The Boolean PRG hop between all-uniform-public-vector chains is bounded by one Boolean
assumption advantage, for every NUPPT realising the explicit advised function.
[JLS26, Lemma 4.2, p. 19]. Dv8 retains the bucket map; Dv12 fixes averaged-out data in
advice. Dv14 assumes the realiser, and Dv16 uses the shared predicate only on encoded
challenges and layout-length coins, strengthening the every-realiser conclusion.

**Proof sketch.** At each Boolean parameter, average over bucket maps, public matrices and
uniform public vectors, and fix advice whose absolute acceptance gap dominates the average.
At image parameters use kappaOfN_n and the preprocessing readers to identify the canonical
Boolean challenge with the two chain endpoints. Transport the realiser's typed coins through
RealizesOn's published readers and remove the unused coin suffix using the existing prefix
sampling lemma. Choose arbitrary inhabited advice off the image and assemble the family. -/
theorem prg_hop (P : Params) (π : PrimeSchedule) (A : NUPPT) :
    ∃ ω : ∀ N, P.PRGAdvice π N, ∀ B : NUPPT,
      B.RealizesOn P.prgEnc (A.coins.subst .var)
        (fun N x r => P.prgRed π A N (ω N) x r) →
      ∀ κ, Games.advantage (P.chainGame A true κ κ (π κ))
          (P.chainGame A false κ κ (π κ)) ≤ P.G.adv B (P.n κ) := sorry

end Params

end TCSlib.Cryptography.Obfuscation.StructuredSeed
