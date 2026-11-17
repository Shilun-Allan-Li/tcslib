<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/FriedgutNecessity.lean :: FABL.sum_addressingErrorIndicator_flip -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Error Count Under the Addressing Flip

**Claim.** For an addressing function and any Boolean function $g$ on the same sign cube, summing the error indicator after the addressing flip gives the same total as summing it over the original inputs.

**Proof.** The addressing flip is an equivalence of the finite input cube with itself. Reindex the sum over inputs by this bijection. Each summand in the reindexed sum is exactly the original error indicator evaluated at the corresponding flipped input, so the reindexed sum is the stated sum before the flip.
