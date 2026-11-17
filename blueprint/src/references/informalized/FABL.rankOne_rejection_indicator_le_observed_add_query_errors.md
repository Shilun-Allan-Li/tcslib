<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.rankOne_rejection_indicator_le_observed_add_query_errors -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rejection indicator bound

**Claim.** The rejection indicator after replacing the four field elements by their approximations is bounded by the original rejection indicator plus the four indicators of a changed element.

**Proof.** If any of the four elements changes, its corresponding error indicator is $1$. The left side is always at most $1$, while every term on the right is nonnegative, so the inequality follows. If none changes, the two rejection conditions are identical, and all four error indicators vanish; hence both sides are equal.
