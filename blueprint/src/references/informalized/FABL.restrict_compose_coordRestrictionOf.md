<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.restrict_compose_coordRestrictionOf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composition of Coordinate Restrictions

**Claim.** Applying the fixed assignment outside $J$ and then the coordinate rules agrees with restricting first to $J$, reindexing its free coordinates, and applying the corresponding rules there.

**Proof.** It suffices to compare the two functions at an arbitrary binary input. Expand the definitions of restriction and reindexed restriction. The complete sign vector produced by composing the outside assignment with the second coordinate rules is, by the composition law for completion (`complete_compose_coordRestrictionOf`), the sign vector obtained by combining the fixed signs outside $J$ with the completion of the reindexed input under the corresponding rules. Evaluating $f$ on these equal sign vectors gives the claimed equality; the reindexed restriction evaluation is precisely the latter evaluation by its defining application rule (`reindexedSignRestriction_apply`).

**Key facts.** `FABL.complete_compose_coordRestrictionOf`, `FABL.reindexedSignRestriction_apply`.
