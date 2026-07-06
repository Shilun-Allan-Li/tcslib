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

## Main results

- `CommunicationComplexity.coinTapeMeasure`: The uniform probability measure on `CoinTape n`, treating every outcome of `n` independent fair coin flips as equally likely.
- `CommunicationComplexity.coinTapeIsProbabilityMeasure`: The uniform measure on `CoinTape n` is a probability measure.

## References

- Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

namespace CommunicationComplexity

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
