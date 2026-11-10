/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.LWE.Assumption
import Mathlib.Tactic.Simps.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Explicit sample schedules for decisional LWE

## Main definitions

* `Parameters.withSamples`: replace only the number of common-secret samples.
* `Family.withSamples`: replace a family's sample schedule by a syntactic polynomial.
* `multiMessageSamples`: the rows needed for `Q(κ) + 1` messages of `κ` bits each.

## Main results

The non-simp projection equations expose every data field of the replacements.
`multiMessageSamples_eval` reads the exact batch count.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Definition 4.2.3 (sample-count parameter).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Definition 93.1 (`Q(κ) + 1` common-key messages).
* [Wu24] D. Wu, CS395T *Topics in Cryptography*, Spring 2024 lecture notes,
  compilation last updated 30 April 2024, Definition 20.5 (one fresh row per bit).

**Convention.** `DLWEAssumption F` retains its audited fixed-sample meaning.
A consumer requiring hardness for every polynomial sample schedule states the
additional hypothesis `∀ M : PolyExpr, DLWEAssumption (F.withSamples M)` explicitly.
No sample-extension, noise-change, parameter-computability or hardness theorem is asserted.
-/

namespace TCSlib.Cryptography.LWE

open Complexity

namespace Parameters

/-- Replace the sample count by `m`, retaining dimension and modulus exactly
[Pei16, Definition 4.2.3, parameter bookkeeping]. -/
def withSamples (P : Parameters) (m : ℕ) : Parameters where
  dimension := P.dimension
  samples := m
  modulus := P.modulus
  modulus_ge_two := P.modulus_ge_two

attribute [simps (config := { isSimp := false }) dimension samples modulus] withSamples

end Parameters

namespace Family

/-- Replace the sample schedule by `M.eval`, retaining the actual dimension,
modulus, scalar noise law and residue width [Pei16, Definition 4.2.3]. The new
sample bound is exactly `M`; this definition asserts no sample amplification. -/
def withSamples (F : Family) (M : PolyExpr) : Family where
  parameters := fun κ => (F.parameters κ).withSamples (M.eval κ)
  noise := F.noise
  dimensionBound := F.dimensionBound
  samplesBound := M
  residueBits := F.residueBits
  dimension_le := F.dimension_le
  samples_le := fun _ => le_rfl
  modulus_le_pow := F.modulus_le_pow

attribute [simps (config := { isSimp := false }) parameters noise dimensionBound
  samplesBound residueBits] withSamples

end Family

/-- Encrypting `Q(κ) + 1` messages with `κ` fresh rows per message requires
`κ * (Q(κ) + 1)` rows under one secret [PS10, Definition 93.1; Wu24, Definition 20.5,
bitwise batching]. This is a count, not an assumption that one fixed schedule suffices. -/
def multiMessageSamples (Q : PolyExpr) : PolyExpr :=
  .mul .var (.add Q (.const 1))

/-- The sample-budget expression is `var * (Q + 1)`. -/
theorem multiMessageSamples_eq (Q : PolyExpr) :
    multiMessageSamples Q = .mul .var (.add Q (.const 1)) := rfl

/-- The sample budget evaluates to `κ * (Q.eval κ + 1)`, including the last
message in the existing multi-message experiment. -/
theorem multiMessageSamples_eval (Q : PolyExpr) (κ : ℕ) :
    (multiMessageSamples Q).eval κ = κ * (Q.eval κ + 1) := by
  rw [multiMessageSamples_eq, PolyExpr.eval_mul, PolyExpr.eval_var,
    PolyExpr.eval_add, PolyExpr.eval_const]

end TCSlib.Cryptography.LWE
