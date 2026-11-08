<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPEval.lean :: Randomized.PIT.lt_of_mem_evalVals -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Range of evaluated gate values

**Claim.** For positive $k$, every value in the list obtained by evaluating the gates modulo $k$ from the empty initial list is strictly less than $k$.

**Proof.** Apply the range component of the evaluation correspondence `Randomized.PIT.map_evalVals` to the empty initial list. Its entries vacuously satisfy the required bound, so the lemma says every entry of the resulting evaluation list is less than $k$.

**Key facts.** `Randomized.PIT.map_evalVals`.
