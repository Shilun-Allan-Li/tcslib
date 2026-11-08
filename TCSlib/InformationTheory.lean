/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.InformationTheory.FinDist
import TCSlib.InformationTheory.StatisticalDistance
import TCSlib.InformationTheory.UniversalHashing
import TCSlib.InformationTheory.LeftoverHash
import TCSlib.InformationTheory.Entropy
import TCSlib.InformationTheory.Extractors
import TCSlib.InformationTheory.Samples

/-!
# Information theory

Finite distributions, statistical distance, entropy, and randomness extraction.

## Contents

* `TCSlib.InformationTheory.FinDist`: distributions on a finite type, collision probability,
  min-entropy.
* `TCSlib.InformationTheory.StatisticalDistance`: statistical distance and the `ℓ¹`–`ℓ²` bound.
* `TCSlib.InformationTheory.UniversalHashing`: universal hash families.
* `TCSlib.InformationTheory.LeftoverHash`: the leftover hash lemma.
* `TCSlib.InformationTheory.Entropy`: Shannon entropy, min-entropy, `k`-sources and flat sources.
* `TCSlib.InformationTheory.Extractors`: `ε`-closeness (equivalent to a statistical-distance
  bound), deterministic and strong extractors, and the leftover hash lemma as an extractor.
* `TCSlib.InformationTheory.Samples`: expectations, the complement rule, iterated expectations
  over products, and `m` independent samples.

## References

* [Vad12] S. Vadhan, *Pseudorandomness*, FnTTCS 7(1–3), 2012.
* [HILL99] J. Håstad, R. Impagliazzo, L. Levin, M. Luby, *A pseudorandom generator from any
  one-way function*, SICOMP 28(4), 1999.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
* [SSBD14] S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*, Cambridge University Press, 2014.
-/
