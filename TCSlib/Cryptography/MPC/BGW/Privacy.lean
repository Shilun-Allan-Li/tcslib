/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecretSharing.Vector
import TCSlib.Cryptography.MPC.BGW.Protocol

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Privacy of BGW on multiplication-free circuits

A circuit without multiplication gates is evaluated by BGW without any interaction: every party
computes its share of every wire from its own shares of the inputs (`bgwEval_congr_of_isLinear`).
Consequently the entire view of a coalition of at most `k - 1` parties is a function of their
input shares alone, and those are independent of the inputs by joint Shamir privacy
(`Shamir.vecScheme_perfectPrivacy`). That gives perfect privacy for this class of circuits, in
the same randomness-bijection form used throughout `TCSlib.Cryptography.SecretSharing`.

**Scope.** Privacy in the presence of multiplication gates is *not* proved here. There the
adversary additionally sees the re-sharings sent at each multiplication gate, and the standard
proof is a simulation argument that re-randomizes those messages; formalizing it needs a model of
the protocol's randomness and a simulator, and is left for future work. What is proved here is
the interaction-free half, plus the degree-reduction algebra in
`TCSlib.Cryptography.MPC.BGW.Protocol` that the simulation argument would sit on top of.

## Main results

* `TCSlib.MPC.BGW.bgwEval_congr_of_isLinear`: a party's share of any wire of a multiplication-free
  circuit depends only on that party's input shares.
* `TCSlib.MPC.BGW.linear_perfectPrivacy`: for at most `k - 1` corrupted parties and any two input
  vectors, a bijection of the dealer's coins leaves the coalition's view of every
  multiplication-free circuit unchanged.

## References

* [BGW88] M. Ben-Or, S. Goldwasser, A. Wigderson, *Completeness theorems for non-cryptographic
  fault-tolerant distributed computation*, STOC 1988, §3.
* [AL17] G. Asharov, Y. Lindell, *A full proof of the BGW protocol for perfectly secure
  multiparty computation*, J. Cryptology 30(1), 2017, §4.
-/

namespace TCSlib.MPC.BGW

open Finset TCSlib.Shamir TCSlib.SecretSharing

variable {F : Type*} [Field F] [DecidableEq F] {ι : Type*} {d k : ℕ}
variable (R : Resharer F d) (A : Finset (Party F))

/-- **Locality of multiplication-free circuits.** Party `j`'s share of a wire of a
multiplication-free circuit is determined by `j`'s own shares of the inputs: no interaction, and
in particular nothing about the other parties' shares, enters it.

**Proof sketch.** Induction on the circuit; every gate other than multiplication acts on share
vectors pointwise, so the value at `j` is computed from values at `j`. -/
theorem bgwEval_congr_of_isLinear (inp inp' : ι → Party F → F) (j : Party F)
    (h : ∀ x, inp x j = inp' x j) :
    ∀ C : Circuit F ι, C.IsLinear → bgwEval R A inp C j = bgwEval R A inp' C j
  | .input x, _ => h x
  | .const _, _ => rfl
  | .add a b, hC => by
      simp only [bgwEval_add, Pi.add_apply]
      rw [bgwEval_congr_of_isLinear inp inp' j h a hC.1,
        bgwEval_congr_of_isLinear inp inp' j h b hC.2]
  | .smul c a, hC => by
      simp only [bgwEval_smul]
      rw [bgwEval_congr_of_isLinear inp inp' j h a hC]
  | .mul _ _, hC => absurd hC not_false

/-- The input share vectors handed to the protocol by the vector dealer. -/
noncomputable def dealtInputs (k : ℕ) (F : Type*) [Field F] [DecidableEq F] (ι : Type*)
    (v : ι → F) (q : ι → Polynomial.degreeLT F (k - 1)) : ι → Party F → F :=
  fun x i => (vecScheme k F ι).share v q i x

/-- **Perfect privacy of BGW on multiplication-free circuits.** For any coalition `B` of at most
`k - 1` parties and any two input vectors `v`, `v'`, there is a bijection of the dealer's coins
under which the coalition's shares of *every* wire of *every* multiplication-free circuit are
literally unchanged. So no such execution tells the coalition anything about the inputs.

**Proof sketch.** Joint Shamir privacy supplies a bijection of the coin vectors making the
coalition's input shares identical under `v` and `v'`. A multiplication-free circuit is evaluated
locally, so each corrupted party's share of each wire is a function of exactly those input
shares, and hence is unchanged too. -/
theorem linear_perfectPrivacy {B : Finset (Party F)} (hB : #B < k) (v v' : ι → F) :
    ∃ e : (ι → Polynomial.degreeLT F (k - 1)) ≃ (ι → Polynomial.degreeLT F (k - 1)),
      ∀ (q : ι → Polynomial.degreeLT F (k - 1)) (i : Party F), i ∈ B →
        ∀ C : Circuit F ι, C.IsLinear →
          bgwEval R A (dealtInputs k F ι v' (e q)) C i
            = bgwEval R A (dealtInputs k F ι v q) C i := by
  have hnot : ¬ (AccessStructure.threshold k).Auth B := by
    simpa using Nat.not_le.2 hB
  obtain ⟨e, he⟩ := vecScheme_perfectPrivacy (F := F) (ι := ι) (k := k) B hnot v v'
  refine ⟨e, fun q i hi C hC => ?_⟩
  refine bgwEval_congr_of_isLinear R A _ _ i (fun x => ?_) C hC
  exact congrFun (he q i hi) x

end TCSlib.MPC.BGW
