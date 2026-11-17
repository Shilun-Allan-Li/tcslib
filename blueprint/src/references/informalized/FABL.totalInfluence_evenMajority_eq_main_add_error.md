<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/EvenMajority.lean :: FABL.totalInfluence_evenMajority_eq_main_add_error -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Even Majority Error Decomposition

**Claim.** For every $m$ and Boolean function $f$ on the $(2m+2)$-dimensional cube, its total influence is the stated main term plus the error defined as the difference between its total influence and that main term.

**Proof.** By definition, the error is the total influence minus the main term. Adding the main term back gives the total influence, by cancellation.
