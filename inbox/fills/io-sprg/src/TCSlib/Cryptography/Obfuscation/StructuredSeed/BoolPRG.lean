/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.CoinSampling.Contract
import TCSlib.Cryptography.Games.Advantage
import TCSlib.Cryptography.Foundations.Subexponential
import TCSlib.Cryptography.Obfuscation.StructuredSeed.PolyTerms
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.MvPolynomial.Eval

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Boolean pseudorandom generators

## Main definitions

* `BoolPRG`: the efficient Boolean generator with an exact index draw and core.
* `BoolPRG.Secure`, `BoolPRG.SubexpSecure`, `BoolPRG.HasStretch`: security and stretch.
* `BoolPRG.MultilinearRep`: integer multilinear output polynomials.
* `BoolPRG.MultilinearRep.HasLocality`, `.TermsEfficient`: locality and generation targets.

## Main results

Owner-side readers expose every new definition.

## References

* [JLS26] A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Well-Founded Assumptions*, J. ACM 73(1), Article 1, February 2026, Sections 2-4.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
  3rd ed., January 2010, Definition 26.8 (non-uniform PPT adversaries).
-/

namespace TCSlib.Cryptography.Obfuscation.StructuredSeed

open Complexity Turing Games

/-- A Boolean generator has an exactly uniform Boolean seed and a sampled function index,
with uniformly efficient index sampling and evaluation. [JLS26, Definition 3.4, p. 11].
Deviations Dv4 and Dv17: the family is indexed by seed length, and index sampling is a
core applied to one exact finite draw; efficiency uses the shared sampler contract.
Disclosed pre-M0 refinement: supplied finite-coordinate equivalences and injective encodings
retain the complete index and draw instead of hiding data in encoding collisions. -/
structure BoolPRG where
  /-- The function-index type at seed length `n`. -/
  Idx : ℕ → Type
  /-- The explicit size of the index coordinate type. -/
  idxCard : ℕ → ℕ
  /-- A supplied finite-coordinate equivalence, never a chosen enumeration. -/
  idxEquiv : (n : ℕ) → Idx n ≃ Fin (idxCard n)
  /-- The index type is finite. -/
  idxFintype : ∀ n, Fintype (Idx n)
  /-- The index type is nonempty. -/
  idxNonempty : ∀ n, Nonempty (Idx n)
  /-- The one exact draw used by index sampling. -/
  IdDraw : ℕ → Type
  /-- The explicit size of the index draw coordinate type. -/
  idDrawCard : ℕ → ℕ
  /-- A supplied finite-coordinate equivalence for the exact draw. -/
  idDrawEquiv : (n : ℕ) → IdDraw n ≃ Fin (idDrawCard n)
  /-- Every index draw type is finite. -/
  idDrawFintype : ∀ n, Fintype (IdDraw n)
  /-- Every index draw type is nonempty. -/
  idDrawNonempty : ∀ n, Nonempty (IdDraw n)
  /-- The deterministic index-sampling core. -/
  idCore : (n : ℕ) → IdDraw n → Idx n
  /-- The explicit encoding of an index draw. -/
  encIdDraw : (n : ℕ) → IdDraw n → List Bool
  /-- The draw encoding retains the complete draw. -/
  encIdDraw_injective : ∀ n, Function.Injective (encIdDraw n)
  /-- The string representation of a function index. -/
  encIdx : (n : ℕ) → Idx n → List Bool
  /-- The function index is received completely as a string. -/
  encIdx_injective : ∀ n, Function.Injective (encIdx n)
  /-- A polynomial bound on the index encoding. -/
  idxBits : PolyExpr
  /-- Every encoded index satisfies the stated bound. -/
  encIdx_length_le : ∀ n I, (encIdx n I).length ≤ idxBits.eval n
  /-- The generator's output length. -/
  outLen : ℕ → ℕ
  /-- A polynomial bound on output length. -/
  outBound : PolyExpr
  /-- The output length satisfies its bound. -/
  outLen_le : ∀ n, outLen n ≤ outBound.eval n
  /-- Evaluation on a Boolean seed. -/
  eval : (n : ℕ) → Idx n → (Fin n → Bool) → Fin (outLen n) → Bool
  /-- One uniform polynomial-time map computes every evaluation. -/
  eval_eff : ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
    ∀ n I σ, f (NUPPT.advInput n (pairEncode (encIdx n I) (List.ofFn σ))) =
      List.ofFn (eval n I σ)
  /-- Index sampling is efficient on its actual exact draw and deterministic core.
  The parameter word includes unary `n`, since the draw type can depend on `n`. -/
  idSamp_eff : CoinSampling.SamplesEfficiently
    (fun n (_ : Unit) => List.replicate n true)
    (fun n _ d => encIdDraw n d) (fun n _ I => encIdx n I) (fun n _ d => idCore n d)

instance instBoolPRGIdxFintype (G : BoolPRG) (n : ℕ) : Fintype (G.Idx n) :=
  G.idxFintype n
instance (G : BoolPRG) (n : ℕ) : Nonempty (G.Idx n) := G.idxNonempty n
instance instBoolPRGIdDrawFintype (G : BoolPRG) (n : ℕ) : Fintype (G.IdDraw n) :=
  G.idDrawFintype n
instance (G : BoolPRG) (n : ℕ) : Nonempty (G.IdDraw n) := G.idDrawNonempty n

/-- The Boolean index finiteness instance is its supplied primitive field; glue. -/
theorem instBoolPRGIdxFintype_eq (G : BoolPRG) (n : ℕ) :
    instBoolPRGIdxFintype G n = G.idxFintype n := rfl

/-- The Boolean index-draw finiteness instance is its supplied primitive field; glue. -/
theorem instBoolPRGIdDrawFintype_eq (G : BoolPRG) (n : ℕ) :
    instBoolPRGIdDrawFintype G n = G.idDrawFintype n := rfl

namespace BoolPRG

/-- The index sampler is the core applied to one uniform draw:
`idSamp n = sample (IdDraw n) >>= fun d => pure (idCore n d)`.
[JLS26, Definition 3.4, p. 11]. Deviation Dv17: the exact-law core-and-draw interface
makes the efficiency field refer to this actual law. -/
noncomputable def idSamp (G : BoolPRG) (n : ℕ) : ProbComp (G.Idx n) :=
  (ProbComp.sample (G.IdDraw n)).bind fun d => .pure (G.idCore n d)

/-- The index law is the pushforward of its uniform draw by `idCore`; glue. -/
theorem idSamp_eq (G : BoolPRG) (n : ℕ) :
    G.idSamp n = (ProbComp.sample (G.IdDraw n)).bind fun d => .pure (G.idCore n d) := rfl

/-- Uniform evaluation efficiency is one map computing all indexed evaluations:
`∃ f, PolyTimeComputable f ∧ ∀ n I σ, f ⟨1^n,⟨I,σ⟩⟩ = Eval(I,σ)`.
[JLS26, Definition 3.4, p. 11]. The unary parameter is explicit; no advice is supplied. -/
def EvalEfficient (G : BoolPRG) : Prop :=
  ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
    ∀ n I σ, f (NUPPT.advInput n (pairEncode (G.encIdx n I) (List.ofFn σ))) =
      List.ofFn (G.eval n I σ)

/-- Evaluation efficiency is exactly the single-map input/output contract; glue. -/
theorem evalEfficient_iff (G : BoolPRG) :
    G.EvalEfficient ↔ ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
      ∀ n I σ, f (NUPPT.advInput n (pairEncode (G.encIdx n I) (List.ofFn σ))) =
        List.ofFn (G.eval n I σ) := Iff.rfl

/-- Every Boolean primitive carries its evaluation-efficiency witness; glue. -/
theorem evalEfficient (G : BoolPRG) : G.EvalEfficient := G.eval_eff

/-- The challenge is `⟨encIdx I, List.ofFn z⟩` for an index and Boolean output vector.
[JLS26, Definitions 3.2 and 3.4, pp. 10-11]. The Boolean assumption has no field modulus;
its canonical challenge therefore contains only the index and output. -/
def challengeStr (G : BoolPRG) (n : ℕ) (I : G.Idx n) (z : Fin (G.outLen n) → Bool) :
    List Bool := pairEncode (G.encIdx n I) (List.ofFn z)

/-- The Boolean challenge is the pair of encoded index and output; glue. -/
theorem challengeStr_eq (G : BoolPRG) (n : ℕ) (I : G.Idx n)
    (z : Fin (G.outLen n) → Bool) :
    G.challengeStr n I z = pairEncode (G.encIdx n I) (List.ofFn z) := rfl

/-- The real/random game gives the adversary a sampled index and either the generator output
on a uniform seed or an independent uniform output. [JLS26, Definitions 3.2 and 3.4,
pp. 10-11]. Deviation Dv4: the security parameter is the Boolean seed length `n`. -/
noncomputable def game (G : BoolPRG) (A : NUPPT) (real : Bool) (n : ℕ) : ProbComp Bool :=
  (G.idSamp n).bind fun I =>
  (ProbComp.sample (Fin n → Bool)).bind fun σ =>
  (ProbComp.sample (Fin (G.outLen n) → Bool)).bind fun u =>
  (ProbComp.sample (A.Coins n)).bind fun r =>
    .pure (A.distinguisherL n (G.challengeStr n I (if real then G.eval n I σ else u)) r)

/-- The game samples the actual index law, seed, comparison output, and adversary coins; glue. -/
theorem game_eq (G : BoolPRG) (A : NUPPT) (real : Bool) (n : ℕ) :
    G.game A real n =
      (G.idSamp n).bind fun I =>
      (ProbComp.sample (Fin n → Bool)).bind fun σ =>
      (ProbComp.sample (Fin (G.outLen n) → Bool)).bind fun u =>
      (ProbComp.sample (A.Coins n)).bind fun r =>
        .pure (A.distinguisherL n
          (G.challengeStr n I (if real then G.eval n I σ else u)) r) := rfl

/-- The Boolean PRG advantage is the absolute real/random acceptance gap.
[JLS26, Definitions 2.1 and 3.4, pp. 8-11]. Deviation Dv4: absolute advantage against
non-uniform PPT machines is the library convention. -/
noncomputable def adv (G : BoolPRG) (A : NUPPT) (n : ℕ) : ℝ :=
  Games.advantage (G.game A true n) (G.game A false n)

/-- The advantage is `Games.advantage` of the two games; glue. -/
theorem adv_eq (G : BoolPRG) (A : NUPPT) (n : ℕ) :
    G.adv A n = Games.advantage (G.game A true n) (G.game A false n) := rfl

/-- Boolean PRG security means negligible advantage for every non-uniform PPT machine:
`Secure G ↔ ∀ A, Negligible (G.adv A)`. [JLS26, Definitions 2.1 and 3.4, pp. 8-11]. -/
def Secure (G : BoolPRG) : Prop := ∀ A : NUPPT, Negligible (G.adv A)

/-- Security is negligible advantage for every non-uniform PPT machine; glue. -/
theorem secure_iff (G : BoolPRG) : G.Secure ↔ ∀ A : NUPPT, Negligible (G.adv A) := Iff.rfl

/-- Subexponential Boolean security is exactly `SubexpHard G.adv`.
[JLS26, Remark 2.1 and Theorem 4.1, pp. 9 and 11]. Deviation Dv13: adversaries remain NUPPT
machines, using the shared advantage notion. -/
def SubexpSecure (G : BoolPRG) : Prop := SubexpHard G.adv

/-- Subexponential Boolean security uses the shared `SubexpHard` predicate; glue. -/
theorem subexpSecure_iff (G : BoolPRG) : G.SubexpSecure ↔ SubexpHard G.adv := Iff.rfl

/-- Stretch at least `τ` means `n^τ ≤ outLen n` at every seed length.
[JLS26, Definition 3.4 and Theorem 4.1, p. 11]. Deviation Dv5: an inequality replaces
`m = n^τ`, avoiding truncation of the supplied generator. -/
def HasStretch (G : BoolPRG) (τ : ℝ) : Prop := ∀ n : ℕ, (n : ℝ) ^ τ ≤ G.outLen n

/-- Stretch is the pointwise lower bound `n^τ ≤ outLen n`; glue. -/
theorem hasStretch_iff (G : BoolPRG) (τ : ℝ) :
    G.HasStretch τ ↔ ∀ n : ℕ, (n : ℝ) ^ τ ≤ G.outLen n := Iff.rfl

/-- A degree-`d` multilinear representation supplies integer polynomials whose Boolean-cube
values equal the output bits. [JLS26, Definition 3.4, p. 11]. Deviation Dv4: the representation
is data for every index, and locality is measured on its variables; semantic uniqueness is
not an additional theorem of this development. -/
structure MultilinearRep (G : BoolPRG) (d : ℕ) where
  /-- An integer polynomial for every output coordinate. -/
  poly : (n : ℕ) → G.Idx n → Fin (G.outLen n) → MvPolynomial (Fin n) ℤ
  /-- Every polynomial is multilinear. -/
  poly_mem_restrictDegree : ∀ n I j, poly n I j ∈ MvPolynomial.restrictDegree (Fin n) ℤ 1
  /-- Every polynomial has total degree at most `d`. -/
  totalDegree_poly_le : ∀ n I j, (poly n I j).totalDegree ≤ d
  /-- On Boolean assignments, the polynomial returns the output bit as an integer. -/
  eval_poly : ∀ n I σ j,
    MvPolynomial.eval (fun i => ((σ i).toNat : ℤ)) (poly n I j) =
      ((G.eval n I σ j).toNat : ℤ)

namespace MultilinearRep

/-- Locality at most `cLoc` means every output polynomial uses at most `cLoc` variables.
[JLS26, Definition 3.4, p. 11]. Deviation Dv4: locality is read on the supplied multilinear
representation, for every index rather than only those in the sampling support. -/
def HasLocality {G : BoolPRG} {d : ℕ} (R : G.MultilinearRep d) (cLoc : ℕ) : Prop :=
  ∀ n I j, (R.poly n I j).vars.card ≤ cLoc

/-- Locality is the variable-cardinality bound for every output coordinate; glue. -/
theorem hasLocality_iff {G : BoolPRG} {d : ℕ} (R : G.MultilinearRep d) (cLoc : ℕ) :
    R.HasLocality cLoc ↔ ∀ n I j, (R.poly n I j).vars.card ≤ cLoc := Iff.rfl

/-- Efficient representation generation uses one polynomial-time map to output an explicit
term list for every polynomial. [JLS26, Section 2, p. 8]. Deviation Dv14: signed integer
coefficients and finite variable coordinates use the explicit `PolyTerms` code.
Phase B obligation; not proved in this development. -/
def TermsEfficient {G : BoolPRG} {d : ℕ} (R : G.MultilinearRep d) : Prop :=
  ∃ f : List Bool → List Bool, PolyTimeComputable f ∧ ∀ n I j,
    ∃ ts : PolyTerms (Fin n) ℤ,
      f (NUPPT.advInput n (pairEncode (G.encIdx n I) (PolyTerms.encFin j))) =
        PolyTerms.encTerms PolyTerms.encInt PolyTerms.encFin ts ∧
      PolyTerms.denote ts = R.poly n I j

/-- Efficient representation generation is exactly the uniform term-list contract; glue. -/
theorem termsEfficient_iff {G : BoolPRG} {d : ℕ} (R : G.MultilinearRep d) :
    R.TermsEfficient ↔
      ∃ f : List Bool → List Bool, PolyTimeComputable f ∧ ∀ n I j,
        ∃ ts : PolyTerms (Fin n) ℤ,
          f (NUPPT.advInput n (pairEncode (G.encIdx n I) (PolyTerms.encFin j))) =
            PolyTerms.encTerms PolyTerms.encInt PolyTerms.encFin ts ∧
          PolyTerms.denote ts = R.poly n I j := Iff.rfl

end MultilinearRep

end BoolPRG

end TCSlib.Cryptography.Obfuscation.StructuredSeed
