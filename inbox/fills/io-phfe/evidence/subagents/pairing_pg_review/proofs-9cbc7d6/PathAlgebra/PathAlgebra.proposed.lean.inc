/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- Proposed headers only; all bodies are deliberately unproved search placeholders.
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Algebra of weighted endpoint matrices

The statements use arbitrary node and edge types, endpoint maps, and ring weights.
They introduce no graph representation or branching-program datatype. The padded
incidence formula abstracts the variable/constant split in [AGW20, Appendix A,
(32), p.38] to an arbitrary ring.

## Main definitions

The matrices are written explicitly in the theorem statements; no new definitions.

## Main results

* `weightedIncidence_mulVec`: forward action of weighted endpoint rows.
* `weightedIncidence_vecMul`: backward action as outgoing minus incoming sums.
* `paddedIncidence_eq`: padded variable/constant matrices equal endpoint rows.

## References

* [AGW20] M. Abdalla, J. Gong, H. Wee, *Functional Encryption for Attribute-Weighted
  Sums from k-Lin*, 2020, Appendix A, (32), p.38.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption
namespace PartialGarbling.PathAlgebra

/-- A weighted endpoint row acts on node values by taking its weighted parent
value minus its child value. No injectivity or distinctness of endpoints is required. -/
theorem weightedIncidence_mulVec {V E R : Type*} [Fintype V] [DecidableEq V]
    [Ring R] (parent child : E → V) (weight : E → R) (values : V → R) :
    Matrix.mulVec
      (Matrix.of fun e v =>
        (if v = parent e then weight e else 0) -
          (if v = child e then 1 else 0)) values =
      fun e => weight e * values (parent e) - values (child e) := sorry

/-- The backward action of weighted endpoint rows is the sum of outgoing
weighted edge values minus the sum of incoming edge values at each node.
Repeated endpoints and loops are permitted; node finiteness is unnecessary. -/
theorem weightedIncidence_vecMul {V E R : Type*} [Fintype E] [DecidableEq V]
    [Ring R] (parent child : E → V) (weight flow : E → R) :
    Matrix.vecMul flow
      (Matrix.of fun e v =>
        (if v = parent e then weight e else 0) -
          (if v = child e then 1 else 0)) =
      fun v =>
        (∑ e, if parent e = v then flow e * weight e else 0) -
          ∑ e, if child e = v then flow e else 0 := sorry

/-- A variable incidence matrix contracted against the public-input tensor,
plus its constant-edge and negative-child entries, equals the weighted endpoint
matrix with the constant 1 appended to the input. This abstracts the split in
[AGW20, Appendix A, (32), p.38] to an arbitrary ring and arbitrary endpoint maps. -/
theorem paddedIncidence_eq {V E R : Type*} [Fintype V] [DecidableEq V]
    [Ring R] {l : ℕ} (parent child : E → V) (label : E → Fin (l + 1))
    (x : Fin l → R) :
    (Matrix.of (fun e (iu : Fin l × V) =>
        if iu.2 = parent e ∧ label e = iu.1.castSucc then (1 : R) else 0) :
          Matrix E (Fin l × V) R) *
      (Matrix.of (fun (iu : Fin l × V) v =>
        x iu.1 * (if iu.2 = v then 1 else 0)) : Matrix (Fin l × V) V R) +
      Matrix.of (fun e v =>
        (if v = parent e ∧ label e = Fin.last l then 1 else 0) -
          (if v = child e then 1 else 0)) =
      Matrix.of (fun e v =>
        (if v = parent e then Fin.snoc x 1 (label e) else 0) -
          (if v = child e then 1 else 0)) := sorry

end PartialGarbling.PathAlgebra
end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption
