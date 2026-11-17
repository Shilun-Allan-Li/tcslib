<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/KKL.lean :: FABL.booleanInfluence_le_maximumInfluence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence bounded by maximum influence

**Claim.** For every coordinate, its influence is at most the maximum influence of the Boolean function over all coordinates.

**Proof.** The maximum influence is the supremum over the finite set of coordinates of their influences, represented as nonnegative reals. Each coordinate belongs to this indexing set, so its value is bounded above by the supremum property of a finite supremum. Viewing that inequality in the reals gives the claim.
