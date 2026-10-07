/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.Classes
import TCSlib.Complexity.CircuitComplexity.PPoly

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Adleman's theorem: BPP ⊆ P/poly

Arora–Barak's Theorem 7.17: every language decidable by a randomized
polynomial-time algorithm has polynomial-size circuits.  The proof is a
counting argument: after error reduction, so few random strings are bad for
any input that one string `r₀` is good for *all* inputs of a given length,
and hardwiring `r₀` turns the verifier into a circuit.

## Main definitions

* `Randomized.VerifierHasCircuits` — "each fixing of the random string turns
  the verifier into a polynomial-size circuit family", the certificate-view
  residue of "`M` is a polynomial-time TM" (see **Deviations**).

## Main results (sorry-stubbed)

* `Randomized.adleman` — [AB09, Thm 7.17].

## Deviations from the source

In [AB09] the verifier is a polynomial-time TM, and the hardwiring step
quotes the simulation of poly-time TMs by poly-size circuits
([AB09, Thm 6.6], `P ⊆ P/poly`).  At this file's abstract level that
simulation enters as the explicit hypothesis
`hCirc : … → VerifierHasCircuits M p` on the efficiency notion `E`; for the
polynomial-time instantiation it is dischargeable from the library's
`Complexity.P_subset_PPoly` tableau machinery (see
`Randomized.PolyTimeModel`).  Circuits are the fan-in-two
`BoolCircuit.DAGCircuit` model of `CircuitComplexity.PPoly`, and the
conclusion is `Language.InPPoly` [AB09, Def 6.5].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open BoolCircuit

variable (E : VerifierModel)

/-- The verifier `M` (with random strings of length `p n` on length-`n`
inputs) turns into polynomial-size circuits when its random string is fixed:
there are constants `a, k` such that for every `n` and every random string
`r` of length `p n`, some well-formed fan-in-two circuit of size at most
`a·(n+1)^k` computes `x ↦ M x r` on length-`n` inputs.  This is what the
polynomial-time simulation [AB09, Thm 6.6] provides for TM verifiers; note
the single size bound uniform in `r`, which the counting argument needs. -/
def VerifierHasCircuits (M : List Bool → List Bool → Bool) (p : ℕ → ℕ) :
    Prop :=
  ∃ a k : ℕ, ∀ (n : ℕ) (r : List Bool), r.length = p n →
    ∃ D : DAGCircuit n,
      D.IsWellFormed ∧ D.IsFaninTwo ∧ D.size ≤ a * (n + 1) ^ k ∧
      ∀ v : Fin n → Bool, D.eval v = M (List.ofFn v) r

/-- **Adleman's theorem: `BPP ⊆ P/poly`** ([AB09, Thm 7.17]).  Relative to
the efficiency notion `E`: if `L ∈ BPP` and `E`-verifiers have circuits when
their random string is fixed (`hCirc`, the residue of [AB09, Thm 6.6]), then
`L` has polynomial-size circuits.

**Proof sketch.** By error reduction ([AB09, Thm 7.10],
`bpp_error_reduction`) take a verifier `M` for `L` with error at most
`2^{-(n+2)}` on inputs of length `n`, using `m = p n` random bits.  Call `r`
*bad* for `x` if `M(x,r) ≠ L(x)`; for each `x` at most `2^m/2^{n+2}` strings
are bad, so at most `2^n · 2^m/2^{n+2} = 2^m/4 < 2^m` strings are bad for
*some* length-`n` input.  Hence some `r₀ ∈ {0,1}^m` is good for every
`x ∈ {0,1}^n`.  By `hCirc`, `x ↦ M x r₀` is computed by a circuit of size
polynomial in `n`, and that circuit decides `L` on length-`n` inputs; the
resulting `DAGCircuitFamily` (one good circuit per length, well-formed and
fan-in-two with the uniform size bound) witnesses `L.InSIZE (polyLen a k)`
and hence `L.InPPoly`. -/
theorem adleman (hMaj : ClosedUnderMajority E) {L : Language Bool}
    (hL : InBPP E L)
    (hCirc : ∀ M a k, E.Eff (boolVerifier M) →
      VerifierHasCircuits M (polyLen a k)) :
    L.InPPoly := by
  sorry

end Randomized
