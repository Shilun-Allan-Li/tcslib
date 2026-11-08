<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPAlgorithms.lean :: FABL.expect_satisfiedIndicators_maxE3Lin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected number of satisfied three-variable constraints

**Claim.** For a finite multiset of three-variable linear constraints, the expected number satisfied by a uniform random assignment is half the multiset's cardinality.

**Proof.** Induct on the multiset. The empty multiset contributes zero, as does its cardinality. For a multiset formed by adjoining one constraint, its total satisfaction count is the new constraint's indicator plus the count for the remaining multiset. Linearity of expectation splits these two contributions. The individual constraint has expected indicator $1/2$ (`expect_satisfiedIndicator_maxE3Lin`), and the induction hypothesis gives half the remaining cardinality. Their sum is half the enlarged cardinality.

**Key facts.** `FABL.expect_satisfiedIndicator_maxE3Lin`.
