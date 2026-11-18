/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- Proposed headers only. No helper proof has been written or checked.
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Weighted prefix conservation

These algebraic statements describe finite prefix tuples and their weighted suffix
completions. The index types and endpoint maps are explicit in the statements; no
graph, branching-program datatype or new algorithm is introduced. They support the
path-sum specialization of [AGW20, Appendix A, (28)–(32), pp.37–38].

## Main definitions

The statements use finite sigma and tuple types directly, without new definitions.

## Main results

* `prefixIncoming_sum`: each non-root prefix is the child of one prefix edge.
* `prefixFlow_balance`: weighted outgoing suffix values and terminal coefficients
  sum to the current suffix value.

## References

* [AGW20] M. Abdalla, J. Gong, H. Wee, *Functional Encryption for Attribute-Weighted
  Sums from k-Lin*, 2020, Appendix A, (28)–(32), pp.37–38.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption
namespace PartialGarbling.PrefixAlgebra

open scoped BigOperators

/-- Every nonempty prefix has exactly one incoming prefix edge, and the empty
prefix has none. Summing values at the child endpoints therefore gives the node
value off the root and zero at the root. This is finite-prefix indexing glue for
the path-sum specialization of [AGW20, Appendix A, (28)–(32), pp.37–38].

**Proof sketch.** Split the dependent finite sum by depth. At a positive node
depth, the successor depth and tuple are uniquely determined; at depth zero no
successor depth matches. Use the published finite-sigma and supported-sum laws. -/
theorem prefixIncoming_sum {I R : Type*} [Fintype I] [DecidableEq I]
    [AddCommMonoid R] (d : ℕ)
    (value : (Σ k : Fin (d + 1), Fin k.val → I) → R)
    (u : Σ k : Fin (d + 1), Fin k.val → I) :
    (∑ e : (Σ k : Fin d, Fin (k.val + 1) → I),
      if (⟨e.1.succ, e.2⟩ : Σ k : Fin (d + 1), Fin k.val → I) = u then
        value ⟨e.1.succ, e.2⟩ else 0) =
      if u = (⟨⟨0, Nat.zero_lt_succ d⟩, Fin.elim0⟩ :
          Σ k : Fin (d + 1), Fin k.val → I) then 0 else value u := sorry

/-- Weighted suffix sums satisfy conservation at every prefix: weighted values
of its children, plus its terminal coefficient when its depth is maximal, equal
its own suffix value. This is the path-sum version of the translation calculation
in [AGW20, Appendix A, (28)–(32), pp.37–38], abstracted to a commutative semiring.

**Proof sketch.** For a nonterminal prefix, split each nonempty suffix into its
first label and remaining tuple using the published tuple equivalence, and split
the label product with Fin.prod_univ_succ. Reassociate prefix extension using
Fin.append_right_cons and its canonical casts. At maximal depth the only suffix
is empty and the only matching terminal coefficient is its own full tuple. -/
theorem prefixFlow_balance {I R : Type*} [Fintype I] [DecidableEq I]
    [CommSemiring R] (d : ℕ) (c : (Fin d → I) → R) (weight : I → R)
    (u : Σ k : Fin (d + 1), Fin k.val → I) :
    let value : (Σ k : Fin (d + 1), Fin k.val → I) → R :=
      fun v => ∑ sigma : Fin (d - v.1.val) → I,
        c (fun i => Fin.append v.2 sigma
          (Fin.cast (Nat.add_sub_of_le (Nat.le_of_lt_succ v.1.isLt)).symm i)) *
            ∏ i : Fin (d - v.1.val), weight (sigma i)
    (∑ e : (Σ k : Fin d, Fin (k.val + 1) → I),
      if (⟨e.1.castSucc, Fin.init e.2⟩ :
          Σ k : Fin (d + 1), Fin k.val → I) = u then
        value ⟨e.1.succ, e.2⟩ * weight (e.2 (Fin.last e.1.val)) else 0) +
      (∑ tau : Fin d → I,
        if u = (⟨Fin.last d, tau⟩ : Σ k : Fin (d + 1), Fin k.val → I) then
          c tau else 0) = value u := sorry

end PartialGarbling.PrefixAlgebra
end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption
