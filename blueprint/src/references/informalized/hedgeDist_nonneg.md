<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Hedge/Basic.lean :: hedgeDist_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of the Hedge Distribution

**Claim.** For each time $t$ and expert $i$, the Hedge distribution satisfies $p_t(i)\geq 0$.

**Proof.** The Hedge weight is strictly positive, as is the potential. A quotient of nonnegative numbers by a positive number is nonnegative, so their ratio, the Hedge distribution, is nonnegative.

**Key facts.** `hedgeWeight_pos`, `potential_pos`.
