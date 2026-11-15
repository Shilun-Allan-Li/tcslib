/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.LearningTheory.PAC.Defs
import TCSlib.LearningTheory.PAC.Prediction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# PAC learning

Probably approximately correct learning over a finite domain, information-theoretic (learners
are arbitrary functions with finite coins), and the prediction game of [PS10, §8.1] with its
bridge to PAC learning.

## Contents

* `TCSlib.LearningTheory.PAC.Defs`: error, labelled samples, PAC, weak and fixed-distribution
  learning, for a given learner at fixed parameters.
* `TCSlib.LearningTheory.PAC.Prediction`: the prediction game; success `= 1 − E[err]`, so
  a small prediction advantage rules out the weak-learning condition under the uniform
  distribution, for that learner, at a confidence below the gap (for a weak learner of
  [KV94, §4.1] whose guarantee is not already that strong, after confidence amplification,
  [KV94, §4.2], which changes the learner).

## References

* [KV94] M. Kearns, U. Vazirani, *An Introduction to Computational Learning Theory*, MIT Press,
  1994.
* [SSBD14] S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*, Cambridge University Press, 2014.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
-/
