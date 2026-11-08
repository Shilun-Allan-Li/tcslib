<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.candidateDecodingEdgeValue_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of edge decoding value

**Claim.** For any family of finite candidate-label sets, default label, vertex, and neighbor in a regular unique game, the expected agreement value obtained by choosing labels from the two candidate sets (using the default when a set is empty) is nonnegative.

**Proof.** For each possible source label, the inner expected value over target labels is nonnegative: each outcome is either the agreement indicator $1$ or $0$. The expectation over a finite candidate set, or the default value when that set is empty, therefore remains nonnegative (`finiteCandidateExpectation_nonneg`). Applying the same nonnegativity fact to the outer expectation over source labels proves that the edge decoding value is nonnegative.

**Key facts.** `FABL.RegularUniqueGame.finiteCandidateExpectation_nonneg`.
