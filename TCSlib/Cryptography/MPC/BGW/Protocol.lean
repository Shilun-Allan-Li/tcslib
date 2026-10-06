/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecretSharing.Sharing
import TCSlib.Cryptography.MPC.ArithmeticCircuit

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The BGW protocol: gate-by-gate evaluation on Shamir shares

The semi-honest BGW protocol evaluates an arithmetic circuit on Shamir-shared inputs, keeping the
invariant that every wire of the circuit is held as a degree-`d` sharing of its true value:

* an addition gate is evaluated by adding shares locally;
* multiplication by a public constant, and introducing a constant, are local;
* a multiplication gate is evaluated by multiplying shares locally — which computes the right
  value but doubles the degree to `2d` — and then *reducing the degree*: every party re-shares
  its product share with a fresh degree-`d` sharing, and all parties take the fixed Lagrange
  combination `∑ λ_i ·` of those re-sharings. This is the only interactive step, and it is why
  BGW needs `2d + 1` honest parties.

The protocol is modelled as a function `bgwEval` from input share vectors to output share
vectors, parameterised by a `Resharer` — the re-sharings the parties contribute at multiplication
gates, which in the real protocol are produced from their private coins. Correctness holds for
*every* resharer, so no probabilistic reasoning is needed for this half of the theorem.

## Main definitions

* `TCSlib.MPC.BGW.Resharer`: a party's ability to produce a degree-`d` sharing of a value it
  holds.
* `TCSlib.MPC.BGW.degreeReduce`: the Lagrange recombination of the parties' re-sharings.
* `TCSlib.MPC.BGW.bgwEval`: the protocol's share-level evaluation of a circuit.

## Main results

* `TCSlib.MPC.BGW.isSharing_degreeReduce`: degree reduction turns a degree-`2d` sharing into a
  degree-`d` sharing of the same value, given `2d + 1` participating parties.
* `TCSlib.MPC.BGW.bgwEval_isSharing`: **correctness invariant** — every wire is a degree-`d`
  sharing of its true value.
* `TCSlib.MPC.BGW.bgwEval_recombine`: **correctness** — the parties' output shares recombine to
  the value the circuit computes.
* `TCSlib.MPC.BGW.bgwEval_of_isLinear`: on a circuit without multiplication gates the protocol is
  non-interactive: the output shares do not depend on the resharer at all.

## References

* [BGW88] M. Ben-Or, S. Goldwasser, A. Wigderson, *Completeness theorems for non-cryptographic
  fault-tolerant distributed computation*, STOC 1988, §3.
* [AL17] G. Asharov, Y. Lindell, *A full proof of the BGW protocol for perfectly secure
  multiparty computation*, J. Cryptology 30(1), 2017, §3–4.
-/

namespace TCSlib.MPC.BGW

open Finset TCSlib.Shamir

variable {F : Type*} [Field F] [DecidableEq F] {ι : Type*} {d : ℕ}

/-- A resharing strategy: each party can turn any value it holds into a degree-`d` sharing of
that value. In the real protocol `reshare i x` is party `i`'s Shamir sharing of `x` using its
private coins; correctness does not care which coins were used, only that the result is a
sharing, so the coins are abstracted away here. [BGW88, §3] -/
structure Resharer (F : Type*) [Field F] (d : ℕ) where
  /-- Party `i`'s degree-`d` sharing of the value `x` it holds. -/
  reshare : Party F → F → Party F → F
  /-- It really is a degree-`d` sharing of `x`. -/
  isSharing_reshare : ∀ i x, IsSharing d x (reshare i x)

variable (R : Resharer F d) (A : Finset (Party F))

/-- The degree reduction step: each party `i ∈ A` re-shares its share `u i`, and the parties take
the Lagrange combination of those re-sharings with the coefficients of `A`. [BGW88, §3] -/
noncomputable def degreeReduce (u : Party F → F) : Party F → F :=
  fun j => ∑ i ∈ A, recombineCoeff A i * R.reshare i (u i) j

/-- **Degree reduction.** If `u` is a degree-`2d` sharing of `z` and at least `2d + 1` parties
take part, then the reduced vector is a degree-`d` sharing of the *same* value `z`. [BGW88, §3],
[AL17, §3.3]

**Proof sketch.** Recombination is a fixed linear functional `∑ λ_i · (−)` of the shares, and by
reconstruction `∑ λ_i · u i = z` because `2d + 1 ≤ #A`. Each summand `λ_i · reshare i (u i)` is a
degree-`d` sharing of `λ_i · u i`, and degree-`d` sharings are closed under sums, so the total is
a degree-`d` sharing of `∑ λ_i · u i = z`. The two uses of linearity — on values and on share
vectors — are the same linear functional, which is the whole trick. -/
theorem isSharing_degreeReduce {z : F} {u : Party F → F} (hu : IsSharing (2 * d) z u)
    (hA : 2 * d + 1 ≤ #A) : IsSharing d z (degreeReduce R A u) := by
  have hsum : IsSharing d (∑ i ∈ A, recombineCoeff A i * u i)
      (fun j => ∑ i ∈ A, recombineCoeff A i * R.reshare i (u i) j) :=
    IsSharing.sum A fun i _ => IsSharing.smul _ (R.isSharing_reshare i (u i))
  have hz : ∑ i ∈ A, recombineCoeff A i * u i = z := hu.recombine_eq hA
  rw [hz] at hsum
  exact hsum

/-- The BGW protocol's share-level evaluation of a circuit: local operations at addition and
constant-multiplication gates, local multiplication followed by degree reduction at
multiplication gates. [BGW88, §3] -/
noncomputable def bgwEval (inp : ι → Party F → F) : Circuit F ι → (Party F → F)
  | .input i => inp i
  | .const c => fun _ => c
  | .add a b => bgwEval inp a + bgwEval inp b
  | .smul c a => fun j => c * bgwEval inp a j
  | .mul a b => degreeReduce R A (bgwEval inp a * bgwEval inp b)

@[simp] theorem bgwEval_input (inp : ι → Party F → F) (i : ι) :
    bgwEval R A inp (.input i) = inp i := rfl
@[simp] theorem bgwEval_const (inp : ι → Party F → F) (c : F) :
    bgwEval R A inp (.const c) = fun _ => c := rfl
@[simp] theorem bgwEval_add (inp : ι → Party F → F) (a b : Circuit F ι) :
    bgwEval R A inp (a.add b) = bgwEval R A inp a + bgwEval R A inp b := rfl
@[simp] theorem bgwEval_smul (inp : ι → Party F → F) (c : F) (a : Circuit F ι) :
    bgwEval R A inp (a.smul c) = fun j => c * bgwEval R A inp a j := rfl
@[simp] theorem bgwEval_mul (inp : ι → Party F → F) (a b : Circuit F ι) :
    bgwEval R A inp (a.mul b) = degreeReduce R A (bgwEval R A inp a * bgwEval R A inp b) := rfl

/-- **Correctness invariant of BGW.** If the inputs are degree-`d` sharings of `v` and at least
`2d + 1` parties take part, then after evaluating any circuit gate by gate, the wire vector is a
degree-`d` sharing of the value that wire carries in the clear. [BGW88, §3], [AL17, Thm 3.1]

**Proof sketch.** Induction on the circuit. Inputs hold by hypothesis and constants are shared by
the constant polynomial. Addition and constant-multiplication preserve both the degree and the
shared value because sharings are closed under those operations. At a multiplication gate the
product of the two share vectors is a degree-`2d` sharing of the product of the values — degrees
add — and degree reduction brings it back to `d` without changing the value. -/
theorem bgwEval_isSharing {v : ι → F} {inp : ι → Party F → F}
    (hinp : ∀ i, IsSharing d (v i) (inp i)) (hA : 2 * d + 1 ≤ #A) :
    ∀ C : Circuit F ι, IsSharing d (C.eval v) (bgwEval R A inp C)
  | .input i => hinp i
  | .const c => isSharing_const d c
  | .add a b => (bgwEval_isSharing hinp hA a).add (bgwEval_isSharing hinp hA b)
  | .smul c a => IsSharing.smul c (bgwEval_isSharing hinp hA a)
  | .mul a b => by
      refine isSharing_degreeReduce R A ?_ hA
      have := (bgwEval_isSharing hinp hA a).mul (bgwEval_isSharing hinp hA b)
      rwa [two_mul]

/-- **Correctness of BGW.** With at least `2d + 1` participating parties, the output shares
produced by the protocol recombine to exactly the value the circuit computes on the inputs.
[BGW88, §3], [AL17, Thm 3.1] -/
theorem bgwEval_recombine {v : ι → F} {inp : ι → Party F → F}
    (hinp : ∀ i, IsSharing d (v i) (inp i)) (hA : 2 * d + 1 ≤ #A) (C : Circuit F ι) :
    recombine A (bgwEval R A inp C) = C.eval v :=
  (bgwEval_isSharing R A hinp hA C).recombine_eq (le_trans (by omega) hA)

/-- On a circuit with no multiplication gates the protocol never uses the resharer: the parties
compute their output shares locally, without interaction. -/
theorem bgwEval_of_isLinear (R' : Resharer F d) (inp : ι → Party F → F) :
    ∀ C : Circuit F ι, C.IsLinear → bgwEval R A inp C = bgwEval R' A inp C
  | .input _, _ => rfl
  | .const _, _ => rfl
  | .add a b, h => by
      rw [bgwEval_add, bgwEval_add, bgwEval_of_isLinear R' inp a h.1,
        bgwEval_of_isLinear R' inp b h.2]
  | .smul c a, h => by
      rw [bgwEval_smul, bgwEval_smul, bgwEval_of_isLinear R' inp a h]
  | .mul _ _, h => absurd h not_false

end TCSlib.MPC.BGW
