/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Probability.UniformOn
import Mathlib.MeasureTheory.Measure.Prod
import TCSlib.CommunicationComplexity.NewmanTheorem.FiniteProbabilitySpace

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# CoinTape: Uniform Probability Measure on Finite Coin Sequences

The random string of a randomized communication protocol [RY20, Ch. 3, §Variants of
Randomized Protocols] is modelled here as a tape of `n` fair coins, i.e. a function
`Fin n → Bool`, carrying the uniform probability measure. Both the public-coin and the
private-coin models of this topic draw their randomness from such tapes.

## Main definitions

- `CommunicationComplexity.CoinTape`: the type `Fin n → Bool` of `n`-bit coin tapes.
- `CommunicationComplexity.coinTapeMeasure`: the uniform probability measure on `CoinTape n`,
  treating every outcome of `n` independent fair coin flips as equally likely (an instance).
- `CommunicationComplexity.coinTapeIsProbabilityMeasure`,
  `CommunicationComplexity.coinTapeFiniteProbabilitySpace`: the uniform measure on
  `CoinTape n` is a probability measure, and `CoinTape n` is a `FiniteProbabilitySpace`
  (instances).

## Main results

None — this file only sets up the coin-tape measure space.

## References

* [RY20] A. Rao, A. Yehudayoff, *Communication Complexity and Applications*,
  Cambridge University Press, 2020.
* [KN97] E. Kushilevitz, N. Nisan, *Communication Complexity*, Cambridge University Press,
  1997.

Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal.
-/

namespace CommunicationComplexity

/-- A coin tape of length `n`: a sequence of `n` bits, one per fair coin flip, i.e. a
function `Fin n → Bool`. This is the random string that a randomized protocol has access to
beyond its inputs [RY20, Ch. 3, Definition (randomized protocol)]; here it consists of `n`
fair bits, uniformly distributed via `coinTapeMeasure`. -/
abbrev CoinTape (n : ℕ) := Fin n → Bool

open MeasureTheory ProbabilityTheory

/-- The uniform probability measure on `CoinTape n`. Every outcome
of `n` independent fair coin flips is equally likely. -/
noncomputable instance coinTapeMeasure (n : ℕ) : MeasureSpace (CoinTape n) where
  volume := uniformOn Set.univ

instance coinTapeIsProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (volume : Measure (CoinTape n)) := by
  change IsProbabilityMeasure (uniformOn Set.univ)
  exact uniformOn_isProbabilityMeasure Set.finite_univ Set.univ_nonempty

noncomputable instance coinTapeFiniteProbabilitySpace (n : ℕ) :
    FiniteProbabilitySpace (CoinTape n) :=
  FiniteProbabilitySpace.of (CoinTape n)

end CommunicationComplexity
