<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/Basic.lean :: FABL.totalInfluence_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of Total Influence

**Claim.** Every real-valued function on a finite-dimensional Boolean cube has nonnegative total influence.

**Proof.** Each coordinate influence is nonnegative (`FABL.influence_nonneg`), since it is an expectation of a square. The total influence is the finite sum of these nonnegative coordinate influences, and is therefore nonnegative.

**Key facts.** `FABL.influence_nonneg`.
