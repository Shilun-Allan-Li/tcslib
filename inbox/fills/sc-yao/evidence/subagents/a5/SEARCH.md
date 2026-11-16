# Reuse search before CoordinateSwap

Searched TCSlib.Cryptography probability/sampling/indistinguishability modules and pinned
Mathlib.Logic.Equiv before coding. Found:

* acceptProb_comp_equiv, Foundations/Experiments.lean:107: exact acceptance invariance under
  any finite seed-space equivalence. Used directly.
* acceptProb_fst, Pseudorandom/Indistinguishability.lean:73: discarding an independent unused
  nonempty seed coordinate. Used directly.
* acceptProb_update, same file:103: single-coordinate independent replacement. Nearest
  existing special case; its probability/counting proof was not copied.
* Games.ProbComp.expect_sample_update and expect_sample_coord, Games/Probability.lean:346/376:
  expectation versions for one coordinate. Not needed or re-proved.
* Mathlib Equiv.prodCongr_apply and Prod.map_apply': public transport equations used directly.
* Mathlib piCongrLeft/piCongrRight/sum-arrow and product equivalences are available to b for
  the concrete key/nonce table shape. This generic law does not duplicate those splits.

No partial matching with a control-dependent selector and padded challenge slots was found.
The new combinatorial argument is only the index-directed swap involution. Its probability
corollaries compose the existing public relabeling and ignored-coordinate theorems.
