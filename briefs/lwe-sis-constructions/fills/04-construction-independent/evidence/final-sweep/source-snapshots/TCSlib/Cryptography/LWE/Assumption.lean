/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.LWE.Encoding
import TCSlib.Cryptography.LWE.Experiments
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Foundations.Negligible

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Fixed-sample decisional LWE against non-uniform PPT machines

## Main definitions

* `TCSlib.Cryptography.LWE.Family`: numeric parameters and scalar noise indexed by a
  separate security parameter, with polynomial dimension, sample and residue-width bounds.
* `Family.inputBitsBound`: a syntactic polynomial bounding the encoded challenge length.
* `Family.advantageAt`: the concrete LWE advantage of a machine on the fixed encoding.
* `DLWEAssumption`: every non-uniform PPT machine has negligible decision advantage.

## Main results

* `Family.inputBitsBound_eq`, `Family.advantageAt_eq`, `dlweAssumption_iff` expose the
  budget and security predicate through their public interfaces.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Definitions 4.2.1 and 4.2.3.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Section 2.1, Definition 26.8 (non-uniform PPT adversaries).

**Scope.** A family fixes one sample schedule. `DLWEAssumption` does not silently quantify
over every polynomial sample schedule. All rows of the experiment use one uniform common
secret, and each error coordinate uses an independent seed for the scalar `Noise` law.
This law is a finite rational distribution, not a claim of exact Gaussian sampling.

The modulus may grow with the parameter, but its chosen binary width is a `PolyExpr` and
the residue-width bound prevents truncation. Polynomial dimension and sample bounds give
a polynomial challenge length, so an adversary's running time in its input length is also
polynomial in the security parameter on these challenges.

`Family` and `DLWEAssumption` assert no efficient parameter generator, residue sampler or
noise sampler. Executable constructions must provide those contracts separately. A first
exact fair-bit implementation can use power-of-two moduli and explicit finite bit-seed
noise; non-dyadic laws require a separate implemented sampler or approximation transfer.
No search-LWE or worst-case lattice reduction is asserted.
-/

namespace TCSlib.Cryptography.LWE

open Complexity

/-- A fixed-sample asymptotic decisional LWE family [Pei16, Definition 4.2.3], using
the repository's non-uniform PPT convention [PS10, Definition 26.8]. The security
parameter is independent of dimension, sample count, modulus and scalar noise.

**Convention.** The syntactic polynomials are upper bounds, not an assertion that the
numeric parameter schedule or noise sampler is uniformly computable. Honest-sampler
efficiency and any statistical approximation are separate construction obligations. -/
structure Family where
  /-- Numeric dimension, sample count and modulus at each security parameter. -/
  parameters : ℕ → Parameters
  /-- The actual scalar finite-seed noise law at each security parameter. -/
  noise : ℕ → Noise
  /-- A syntactic polynomial upper bound on the secret dimension. -/
  dimensionBound : PolyExpr
  /-- A syntactic polynomial upper bound on the fixed sample schedule. -/
  samplesBound : PolyExpr
  /-- The fixed-width binary representation of each residue. -/
  residueBits : PolyExpr
  /-- The dimension is polynomially bounded in the independent security parameter. -/
  dimension_le : ∀ κ, (parameters κ).dimension ≤ dimensionBound.eval κ
  /-- The chosen number of samples is polynomially bounded. -/
  samples_le : ∀ κ, (parameters κ).samples ≤ samplesBound.eval κ
  /-- Every residue fits in the selected width; no modular entry is truncated. -/
  modulus_le_pow : ∀ κ, (parameters κ).modulus ≤ 2 ^ (residueBits.eval κ)

namespace Family

/-- The syntactic polynomial `samplesBound * (dimensionBound + 1) * residueBits`
majorizes the challenge's matrix-plus-vector bit length. This is representation
accounting for the fixed-sample experiment of [Pei16, Definition 4.2.3]. -/
def inputBitsBound (F : Family) : PolyExpr :=
  .mul (.mul F.samplesBound (.add F.dimensionBound (.const 1))) F.residueBits

/-- `F.inputBitsBound` is the expression
`samplesBound * (dimensionBound + 1) * residueBits`. -/
theorem inputBitsBound_eq (F : Family) :
    F.inputBitsBound =
      .mul (.mul F.samplesBound (.add F.dimensionBound (.const 1))) F.residueBits := rfl

/-- Every challenge supplied to a distinguisher fits the family's polynomial input budget.

**Proof sketch.** Substitute `encodeChallenge_length`, bound the dimension and sample
count by the family's fields, and read the multiplication/addition equations of `PolyExpr`.
All factors are natural numbers, so multiplication preserves the inequalities. -/
theorem encodeChallenge_length_le (F : Family) (κ : ℕ)
    (x : Matrix (Fin (F.parameters κ).samples) (Fin (F.parameters κ).dimension)
      (ZMod (F.parameters κ).modulus) ×
      (Fin (F.parameters κ).samples → ZMod (F.parameters κ).modulus)) :
    (encodeChallenge (F.parameters κ) (F.residueBits.eval κ) x).length ≤
      F.inputBitsBound.eval κ := by
  rw [encodeChallenge_length, inputBitsBound_eq, PolyExpr.eval_mul, PolyExpr.eval_mul,
    PolyExpr.eval_add, PolyExpr.eval_const]
  exact Nat.mul_le_mul_right _
    (Nat.mul_le_mul (F.samples_le κ) (Nat.add_le_add_right (F.dimension_le κ) 1))

/-- The decision advantage of a non-uniform PPT machine at security parameter `κ`
on the canonical encoding of `(A,A s+e)` versus uniform `(A,u)`
[Pei16, Definition 4.2.3; PS10, Definition 26.8]. Machine coins are independent of the
matrix, common secret and coordinate-noise seeds. -/
noncomputable def advantageAt (F : Family) (D : NUPPT) (κ : ℕ) : ℝ :=
  decisionAdvantage (F.parameters κ) (F.noise κ)
    (fun x r => D.distinguisherL κ
      (encodeChallenge (F.parameters κ) (F.residueBits.eval κ) x) r)

/-- `F.advantageAt D κ` is `decisionAdvantage` with `D.distinguisherL κ` applied to
the fixed-width challenge encoding. -/
theorem advantageAt_eq (F : Family) (D : NUPPT) (κ : ℕ) :
    F.advantageAt D κ = decisionAdvantage (F.parameters κ) (F.noise κ)
      (fun x r => D.distinguisherL κ
        (encodeChallenge (F.parameters κ) (F.residueBits.eval κ) x) r) := rfl

end Family

/-- The fixed-sample decisional LWE assumption: every non-uniform PPT machine has
negligible absolute decision advantage [Pei16, Definition 4.2.3; PS10, Definition 26.8].
The sample schedule is the one stored in `F.parameters`; a statement for all polynomial
sample schedules requires an additional outer quantifier. This is a proposition supplied
as a hypothesis by consumers, not a theorem or a new axiom. -/
def DLWEAssumption (F : Family) : Prop :=
  ∀ D : NUPPT, Negligible fun κ => F.advantageAt D κ

/-- `DLWEAssumption F` holds exactly when `F.advantageAt D` is negligible for every
non-uniform PPT machine `D`. -/
theorem dlweAssumption_iff (F : Family) :
    DLWEAssumption F ↔ ∀ D : NUPPT, Negligible fun κ => F.advantageAt D κ := Iff.rfl

end TCSlib.Cryptography.LWE
