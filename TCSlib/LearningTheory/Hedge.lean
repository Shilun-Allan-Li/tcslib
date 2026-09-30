/-
Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karim Abdel Sadek, Mark Bedaywi
-/
import TCSlib.LearningTheory.Hedge.Hoeffding
import TCSlib.LearningTheory.Hedge.Basic
import TCSlib.LearningTheory.Hedge.Regret
import TCSlib.LearningTheory.Hedge.Episode
import TCSlib.LearningTheory.Hedge.ConvexPrediction

/-!
# Hedge (Exponentially Weighted Average Forecaster)

Regret bounds for the Hedge / exponentially weighted average algorithm over a finite
set of experts, the adaptive-adversary interaction model, and the convex
prediction-space bridge.

## Contents

- `Hedge.Hoeffding`: Hoeffding's lemma in log-MGF form (weak `η²/2` and tight `η²/8`)
- `Hedge.Basic`: loss sequences, Hedge weights/distribution, regret; potential lemmas
- `Hedge.Regret`: regret bounds `ln N/η + ηT/2` and `ln N/η + ηT/8`, optimized rates
- `Hedge.Episode`: learner policies, adaptive adversaries, generated episodes
- `Hedge.ConvexPrediction`: Jensen bridge to convex losses on weighted-average predictions
-/
