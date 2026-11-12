/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.InformationTheory.FinDist
import TCSlib.InformationTheory.StatisticalDistance
import TCSlib.InformationTheory.UniversalHashing
import TCSlib.InformationTheory.LeftoverHash

/-!
# Information theory

Finite distributions, statistical distance, and randomness extraction.

## Contents

* `TCSlib.InformationTheory.FinDist`: distributions on a finite type, collision probability,
  min-entropy.
* `TCSlib.InformationTheory.StatisticalDistance`: statistical distance and the `ℓ¹`–`ℓ²` bound.
* `TCSlib.InformationTheory.UniversalHashing`: universal hash families.
* `TCSlib.InformationTheory.LeftoverHash`: the leftover hash lemma.

## References

* [Vad12] S. Vadhan, *Pseudorandomness*, FnTTCS 7(1–3), 2012.
* [HILL99] J. Håstad, R. Impagliazzo, L. Levin, M. Luby, *A pseudorandom generator from any
  one-way function*, SICOMP 28(4), 1999.
-/
