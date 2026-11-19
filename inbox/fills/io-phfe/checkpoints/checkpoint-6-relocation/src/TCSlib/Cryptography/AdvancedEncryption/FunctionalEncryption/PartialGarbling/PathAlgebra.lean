/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

open scoped BigOperators Matrix

/-- A weighted endpoint row acts on node values by taking its weighted parent
value minus its child value. No injectivity or distinctness of endpoints is required. 

**Proof sketch.** Identify each row with the difference of its parent and child
coordinate vectors. Apply the published subtraction and single-coordinate dot-product laws. -/
theorem weightedIncidence_mulVec {V E R : Type*} [Fintype V] [DecidableEq V]
    [Ring R] (parent child : E → V) (weight : E → R) (values : V → R) :
    Matrix.mulVec
      (Matrix.of fun e v =>
        (if v = parent e then weight e else 0) -
          (if v = child e then 1 else 0)) values =
      fun e => weight e * values (parent e) - values (child e) :=
  funext fun e =>
    show dotProduct
      (fun v => (if v = parent e then weight e else 0) -
        (if v = child e then 1 else 0)) values =
        weight e * values (parent e) - values (child e) from
      (congrArg (fun row : V → R => dotProduct row values)
        (funext fun v =>
          congrArg₂ (fun a b : R => a - b)
            (Pi.single_apply (parent e) (weight e) v).symm
            (Pi.single_apply (child e) (1 : R) v).symm)).trans
        ((sub_dotProduct (Pi.single (parent e) (weight e))
          (Pi.single (child e) (1 : R)) values).trans
          (congrArg₂ (fun a b : R => a - b)
            (single_dotProduct values (weight e) (parent e))
            (single_one_dotProduct (child e) values)))

/-- The backward action of weighted endpoint rows is the sum of outgoing
weighted edge values minus the sum of incoming edge values at each node.
Repeated endpoints and loops are permitted; node finiteness is unnecessary. 

**Proof sketch.** Distribute the backward matrix action across subtraction. Read each
coordinate through the published vector-matrix action formula and conditional multiplication. -/
theorem weightedIncidence_vecMul {V E R : Type*} [Fintype E] [DecidableEq V]
    [Ring R] (parent child : E → V) (weight flow : E → R) :
    Matrix.vecMul flow
      (Matrix.of fun e v =>
        (if v = parent e then weight e else 0) -
          (if v = child e then 1 else 0)) =
      fun v =>
        (∑ e, if parent e = v then flow e * weight e else 0) -
          ∑ e, if child e = v then flow e else 0 := by
  change Matrix.vecMul flow
    ((Matrix.of fun e v => if v = parent e then weight e else 0) -
      (Matrix.of fun e v => if v = child e then (1 : R) else 0)) = _
  rw [Matrix.vecMul_sub]
  funext v
  simp only [Pi.sub_apply, Matrix.vecMul_eq_sum, Finset.sum_apply, Pi.smul_apply,
    Matrix.of_apply, smul_eq_mul, mul_ite, mul_zero, mul_one, eq_comm]

/-- A variable incidence matrix contracted against the public-input tensor,
plus its constant-edge and negative-child entries, equals the weighted endpoint
matrix with the constant 1 appended to the input. This abstracts the split in
[AGW20, Appendix A, (32), p.38] to an arbitrary ring and arbitrary endpoint maps. 

**Proof sketch.** Contract the product-indexed matrix using the published finite-sum
readers. Split the edge label into a variable coordinate or the final constant coordinate;
the corresponding one-coordinate sum yields the padded input value. -/
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
        (if v = parent e then Fin.snoc (α := fun _ => R) x (1 : R) (label e) else 0) -
          (if v = child e then 1 else 0)) := by
  funext e v
  -- Contract the product index and its single supported node coordinate.
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply,
    Fintype.sum_prod_type, ite_and, ite_mul, one_mul, zero_mul,
    Fintype.sum_ite_eq']
  have hlast (i : Fin l) : Fin.last l ≠ i.castSucc :=
    Ne.symm (Fin.castSucc_ne_last i)
  -- At the parent column, split the label into variable and constant cases.
  by_cases hv : v = parent e
  · subst v
    generalize label e = a
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simp only [hlast, if_false, if_true, Fin.snoc_last,
        Finset.sum_const_zero, zero_add]
    · simp only [Fin.castSucc_inj, Fin.castSucc_ne_last, if_false,
        Fin.snoc_castSucc, Fintype.sum_ite_eq, if_true, mul_one,
        sub_eq_add_neg, zero_add]
  -- Every other column has zero parent contribution on both sides.
  · simp only [if_neg hv, if_neg (Ne.symm hv), mul_zero, ite_self,
      Finset.sum_const_zero, zero_add]

end PartialGarbling.PathAlgebra
end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption
