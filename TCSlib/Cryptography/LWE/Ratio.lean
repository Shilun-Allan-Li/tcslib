/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.LWE.Assumption

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A polynomially bounded modulus-to-noise ratio for an LWE family

## Main definitions

* `Family.RatioBounded F B p`: at every security parameter `κ` the noise law of `F` is
  `B κ`-bounded and the modulus is at most `p(κ)·B(κ)`, for a syntactic polynomial `p`.

## Main results

* `Family.ratioBounded_iff`: the reader of the predicate.

The predicate is the regime of the phase-5 ruling Q16 (assumption (A2) of the GSW plan): DLWE
for a family whose ratio `q/B` is polynomially bounded. Its consumers are the GSW
polynomial-ratio statements (`GSW/PolyRatio.lean`); no theorem is stated here.

## References

* [BV14] Z. Brakerski, V. Vaikuntanathan, *Lattice-Based FHE as Secure as PKE*, ITCS 2014;
  IACR ePrint 2013/541: §3.4, Thm 3.7 (a noise rate `α` inverse-polynomial in `n log q`).
* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Definition 4.2.3 (decision-LWE).

**Deviations.** [BV14, Thm 3.7] bounds a Gaussian noise rate `α`; here the noise law is the
library's finite-seed `Noise` with a worst-case bound `B`, and the ratio is `q ≤ p(κ)·B(κ)`.
-/

namespace TCSlib.Cryptography.LWE

open Complexity

/-- **A polynomially bounded ratio** (phase-5 Q16; P6-Q12): for every security parameter `κ`,
the noise law `F.noise κ` is `B κ`-bounded and the modulus is at most `p(κ)·B(κ)`,
`F.RatioBounded B p ↔ ∀ κ, (F.noise κ).Bounded (B κ) ∧
(F.parameters κ).modulus ≤ p.eval κ * B κ` [BV14, §3.4, Thm 3.7, p016-b001: the noise rate
`α` inverse-polynomial; Pei16, Def 4.2.3, p024-b001]. Deviation: a worst-case bound on a
finite-seed law instead of a Gaussian rate. -/
def Family.RatioBounded (F : Family) (B : ℕ → ℕ) (p : PolyExpr) : Prop :=
  ∀ κ, (F.noise κ).Bounded (B κ) ∧ (F.parameters κ).modulus ≤ p.eval κ * B κ

/-- `F.RatioBounded B p` holds exactly when, for every `κ`, `(F.noise κ).Bounded (B κ)` and
`(F.parameters κ).modulus ≤ p.eval κ * B κ`. -/
theorem Family.ratioBounded_iff (F : Family) (B : ℕ → ℕ) (p : PolyExpr) :
    F.RatioBounded B p ↔
      ∀ κ, (F.noise κ).Bounded (B κ) ∧ (F.parameters κ).modulus ≤ p.eval κ * B κ :=
  Iff.rfl

end TCSlib.Cryptography.LWE
