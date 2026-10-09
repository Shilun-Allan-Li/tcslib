/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.SchwartzZippel
import TCSlib.Complexity.Randomized.ErrorReduction
import TCSlib.Complexity.Randomized.Classes
import TCSlib.Complexity.Randomized.Adleman
import TCSlib.Complexity.Randomized.SipserGacs
import TCSlib.Complexity.Randomized.PolyTimeModel

/-!
# Randomized Computation

Arora–Barak Chapter 7 (Randomized Computation): the model-free
probabilistic tools, and the chapter's complexity classes and theorems in
the certificate view of [AB09, Def 7.4], relative to an abstract efficiency
notion (`Randomized.VerifierModel`) standing in for polynomial-time Turing
machines.

## Contents

- `Randomized.SchwartzZippel`: the Schwartz–Zippel lemma in Arora–Barak's
  form ([AB09, Lem 7.5]), restated from Mathlib's
  `MvPolynomial.schwartz_zippel_totalDegree`.
- `Randomized.ErrorReduction`: the Chernoff bound for i.i.d. Boolean trials
  ([AB09, Cor 7.11]) and the majority-vote error bound that is the
  calculation inside the error-reduction theorem ([AB09, Thm 7.10]).
- `Randomized.Classes`: verifier-style `BPP`/`RP`/`coRP`/`ZPP`
  ([AB09, Defs 7.1/7.4/7.6/7.7]), `ZPP = RP ∩ coRP` ([AB09, Thm 7.8]), and
  error reduction at the class level ([AB09, Lem 7.9, Thm 7.10]).
- `Randomized.Adleman`: `BPP ⊆ P/poly` ([AB09, Thm 7.17]), concluding in
  `Language.InPPoly` from `CircuitComplexity.PPoly`.
- `Randomized.SipserGacs`: certificate-style `Σ₂ᵖ`/`Π₂ᵖ` and
  `BPP ⊆ Σ₂ᵖ ∩ Π₂ᵖ` ([AB09, Thm 7.18]).
- `Randomized.PolyTimeModel`: the instantiation of the abstract verifier
  model by genuine polynomial-time machines (`Complexity.P`), discharging
  the closure hypotheses and connecting `Σ₂` to `Complexity.SigmaP 2`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/
