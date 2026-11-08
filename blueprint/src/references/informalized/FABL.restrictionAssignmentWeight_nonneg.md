<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/RandomRestrictions.lean :: FABL.restrictionAssignmentWeight_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of ordinary assignment weight

**Claim.** The ordinary assignment weight is nonnegative for every restriction assignment.

**Proof.** Each coordinate weight is nonnegative: it is $1/2$ for a free state and $1/4$ for either fixed state (\texttt{coordRestrictionWeight\_nonneg}). The assignment weight is their finite product, hence is nonnegative.

**Key facts.** `FABL.coordRestrictionWeight_nonneg`.
