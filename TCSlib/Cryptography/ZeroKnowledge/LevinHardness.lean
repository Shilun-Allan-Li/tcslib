/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.Relations
import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.Bridge
import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.Verifier
import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.CircuitWitness
import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.Gadget
import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.UnaryArith
import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.ColoringGraph
import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.ColoringParse
import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.ColoringWitness
import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.Soundness
import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.Padding
import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.Hardness

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# `3COL` is NP-hard with Levin reductions

The string-level Levin reduction of every witness relation to `(3COL, R_3COL)` along the circuit
route [AB09, Lemmas 6.10 and 6.11, p. 111] and the 3SAT → 3-colouring reduction of [St73] in
the course material's variant, which proves `TCSlib.Cryptography.LevinNPHard L3COL R3COL` and
makes [PS10, Theorem 124.1] unconditional.

## Contents

* `Relations` — the witness relations `R_CKT` and `R_3SAT`.
* `Bridge` — quarantined readers for frozen definitions without published readers (bounded
  Rule-10 exception, decision-log row "EF-H12-R1 ruled (A)"; repaid by owner PRs).
* `Verifier` — step 1: certificate, verifier in `P`, tableau instance map [AB09, Lemma 6.10].
* `CircuitWitness` — step 2: the Tseitin map with the wire values as witness [AB09, Lemma 6.11].
* `Gadget` — the course gadget graph laid out on `Fin N`.
* `UnaryArith` — unary arithmetic rows for the gadget layout.
* `ColoringGraph` — step 3: the gadget instance map, its tests and the vertex equivalence.
* `ColoringParse` — step 3: the polynomial-time clause-membership and width tests.
* `ColoringWitness` — step 4: the explicit 3-colouring witness (disclosed re-derivation).
* `Soundness` — soundness transported from the course theorem along a homomorphism.
* `Padding` — isolated-vertex padding of graphs and colourings.
* `Hardness` — the assembly: `levinNPHard_L3COL` and the unconditional corollaries.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (§6.1.2, Lemmas 6.10 and 6.11, p. 111.)
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7, Theorem 124.1.)
* [St73] L. Stockmeyer, *Planar 3-Colorability is Polynomial Complete*, ACM SIGACT News 5(3),
  July 1973, pp. 19–25. (Theorem, p. 22; proof pp. 21–22; Fig. 1, p. 24. The printed pages of
  this issue are bound out of order: the proof of part 1), the reduction from 3SAT, runs from
  p. 22 back to p. 21.)
* CS 294-268 course material (UC Berkeley, Spring 2026, V. Guruswami), the 3SAT →
  3-colouring reduction as formalized in `Complexity/NPReductions/ThreeSATToColoring.lean`.
-/
