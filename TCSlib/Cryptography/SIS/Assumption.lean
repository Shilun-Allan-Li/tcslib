/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SIS.Encoding
import TCSlib.Cryptography.SIS.Experiments
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Foundations.Negligible

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# SIS against non-uniform PPT machines

## Main definitions

* `TCSlib.Cryptography.SIS.Family`: dimension, column count, modulus and squared-norm
  bound at each independent security parameter, with polynomial representation budgets.
* `Family.inputBitsBound`, `Family.outputBitsBound`: syntactic polynomial bounds for
  the matrix input and prescribed signed integer-vector output.
* `Family.successAt`: the concrete success probability of a binary-output machine.
* `SISAssumption`: every non-uniform PPT machine has negligible SIS success.

## Main results

* The budget and success equation lemmas and `sisAssumption_iff` expose the assumption
  without unfolding its definitions.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Definition 4.1.1.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Section 2.1, Definition 26.8 (non-uniform PPT adversaries).

**Representation convention.** Matrix entries use `residueBits` bits each. Solver output
uses one sign bit and `magnitudeBits` bits per integer coordinate, with malformed total
lengths rejected. The family requires
`sqNormBound < 2^magnitudeBits`, a conservative sufficient numeric condition that covers
the magnitude of every vector satisfying the norm bound. This prevents the output format
from silently excluding otherwise valid solutions. No solution-completeness theorem is
assumed here; its encoding proof is a separate statement-gate obligation.

These are mathematical finite-distribution experiments. Efficient parameter generation,
matrix sampling and implementation of encoders/decoders remain separate construction
obligations. In particular an exact fair-bit matrix sampler needs a power-of-two modulus
or a separate sampling argument. The bundle does not assert that solutions exist or that
the norm bound excludes trivial multiples of the modulus. Parameter profiles must check
those facts separately. SIS hardness is independent of LWE throughout this module.
-/

namespace TCSlib.Cryptography.SIS

open Complexity

/-- An asymptotic SIS family with a separate security parameter
[Pei16, Definition 4.1.1; PS10, Definition 26.8]. Dimensions and representation widths
have syntactic polynomial bounds. The numeric squared-norm bound must fit the output
magnitude width so that short solutions are representable.

**Convention.** This bundle asserts representation bounds, not uniform computability or
efficiency of an honest sampler. Those contracts are separate from hardness. -/
structure Family where
  /-- Numeric dimension, column count, modulus and squared-norm bound. -/
  parameters : ℕ → Parameters
  /-- A syntactic polynomial upper bound on the public matrix's row count. -/
  dimensionBound : PolyExpr
  /-- A syntactic polynomial upper bound on the public matrix's column count. -/
  columnsBound : PolyExpr
  /-- The fixed-width binary representation of each matrix entry. -/
  residueBits : PolyExpr
  /-- The unsigned magnitude width in each signed output coordinate. -/
  magnitudeBits : PolyExpr
  /-- The matrix dimension is polynomially bounded. -/
  dimension_le : ∀ κ, (parameters κ).dimension ≤ dimensionBound.eval κ
  /-- The number of output coordinates is polynomially bounded. -/
  columns_le : ∀ κ, (parameters κ).columns ≤ columnsBound.eval κ
  /-- Every matrix residue fits without truncation. -/
  modulus_le_pow : ∀ κ, (parameters κ).modulus ≤ 2 ^ (residueBits.eval κ)
  /-- Conservative coverage condition: the entire squared-norm bound fits in the
  magnitude width, hence so does every coordinate of a valid solution. -/
  sqNormBound_lt_pow : ∀ κ, (parameters κ).sqNormBound < 2 ^ (magnitudeBits.eval κ)

namespace Family

/-- The syntactic polynomial `dimensionBound * columnsBound * residueBits` bounds
the public SIS matrix encoding [Pei16, Definition 4.1.1, representation accounting]. -/
def inputBitsBound (F : Family) : PolyExpr :=
  .mul (.mul F.dimensionBound F.columnsBound) F.residueBits

/-- `F.inputBitsBound` is the expression
`dimensionBound * columnsBound * residueBits`. -/
theorem inputBitsBound_eq (F : Family) :
    F.inputBitsBound = .mul (.mul F.dimensionBound F.columnsBound) F.residueBits := rfl

/-- The syntactic polynomial `columnsBound * (magnitudeBits + 1)` bounds the prescribed
signed integer-vector output [Pei16, Definition 4.1.1, representation accounting]. -/
def outputBitsBound (F : Family) : PolyExpr :=
  .mul F.columnsBound (.add F.magnitudeBits (.const 1))

/-- `F.outputBitsBound` is the expression `columnsBound * (magnitudeBits + 1)`. -/
theorem outputBitsBound_eq (F : Family) :
    F.outputBitsBound = .mul F.columnsBound (.add F.magnitudeBits (.const 1)) := rfl

/-- Every SIS challenge fits the family's syntactic polynomial input budget.

**Proof sketch.** Substitute `encodeChallenge_length`, apply the numeric dimension and
column bounds, and read `PolyExpr`'s addition/multiplication equations. -/
theorem encodeChallenge_length_le (F : Family) (κ : ℕ)
    (A : Matrix (Fin (F.parameters κ).dimension) (Fin (F.parameters κ).columns)
      (ZMod (F.parameters κ).modulus)) :
    (encodeChallenge (F.parameters κ) (F.residueBits.eval κ) A).length ≤
      F.inputBitsBound.eval κ := by
  sorry

/-- The signed encoding of every candidate fits the prescribed polynomial output budget.

**Proof sketch.** Substitute `encodeSolution_length` and apply `columns_le`, with the
common nonnegative coordinate width `magnitudeBits + 1`. -/
theorem encodeSolution_length_le (F : Family) (κ : ℕ)
    (z : Fin (F.parameters κ).columns → ℤ) :
    (encodeSolution (F.parameters κ) (F.magnitudeBits.eval κ) z).length ≤
      F.outputBitsBound.eval κ := by
  sorry

/-- The SIS success probability of an `NUPPT` at parameter `κ`
[Pei16, Definition 4.1.1; PS10, Definition 26.8]. The machine receives the canonical
public-matrix encoding, and its output is decoded as an exact-length signed integer
vector. A malformed output fails; a decoded output must still satisfy the full integer
solution relation tested by `successProbability`. -/
noncomputable def successAt (F : Family) (D : NUPPT) (κ : ℕ) : ℝ :=
  successProbability (F.parameters κ)
    (fun A r => decodeSolution (F.parameters κ) (F.magnitudeBits.eval κ)
      (D.runAt κ (encodeChallenge (F.parameters κ) (F.residueBits.eval κ) A) r))

/-- `F.successAt D κ` is the concrete SIS success probability with the machine run
on encoded matrices and its output passed through `decodeSolution`. -/
theorem successAt_eq (F : Family) (D : NUPPT) (κ : ℕ) :
    F.successAt D κ = successProbability (F.parameters κ)
      (fun A r => decodeSolution (F.parameters κ) (F.magnitudeBits.eval κ)
        (D.runAt κ (encodeChallenge (F.parameters κ) (F.residueBits.eval κ) A) r)) := rfl

end Family

/-- The SIS assumption for this parameter family: every non-uniform PPT machine has
negligible success at producing a nonzero short integer kernel vector
[Pei16, Definition 4.1.1; PS10, Definition 26.8]. This is a proposition supplied by
consumers, not a theorem, axiom or consequence of the LWE assumption. -/
def SISAssumption (F : Family) : Prop :=
  ∀ D : NUPPT, Negligible fun κ => F.successAt D κ

/-- `SISAssumption F` holds exactly when `F.successAt D` is negligible for every
non-uniform PPT machine `D`. -/
theorem sisAssumption_iff (F : Family) :
    SISAssumption F ↔ ∀ D : NUPPT, Negligible fun κ => F.successAt D κ := Iff.rfl

end TCSlib.Cryptography.SIS
