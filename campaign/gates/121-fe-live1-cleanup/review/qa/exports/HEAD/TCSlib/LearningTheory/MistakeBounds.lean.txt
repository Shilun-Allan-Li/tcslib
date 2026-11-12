/-
Copyright (c) 2026 Arhaan Aggarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arhaan Aggarwal
-/
import TCSlib.LearningTheory.MistakeBounds.Halving
import TCSlib.LearningTheory.MistakeBounds.WeightedMajority

/-!
# Mistake Bounds for Online Classification with Expert Advice

Deterministic mistake bounds for online binary classification over a finite hypothesis
class or a finite set of experts: the realizable case (Halving) and the agnostic case
(Weighted Majority), following Mohri–Rostamizadeh–Talwalkar, *Foundations of Machine
Learning*, §8.2.

## Contents

- `MistakeBounds.Halving`: the Halving algorithm makes at most `log₂ |H|` mistakes in the
  realizable setting
- `MistakeBounds.WeightedMajority`: potential-function mistake bound for Weighted Majority
  (agnostic setting)
-/
