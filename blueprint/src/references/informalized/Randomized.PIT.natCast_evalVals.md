<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPEval.lean :: Randomized.PIT.natCast_evalVals -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation agrees with ring evaluation

**Claim.** For positive $k$, mapping the natural-number evaluation list from the empty initial list into $\mathbb Z/k\mathbb Z$ gives the same list as running the gates in that ring on the reduced inputs.

**Proof.** Use the correspondence `Randomized.PIT.map_evalVals` with the empty initial list. Its initial entries satisfy the required range condition vacuously, and its equality identifies the mapped natural-number evaluation list with the gate fold in $\mathbb Z/k\mathbb Z$. That fold is precisely the specified ring-valued run from the empty list.

**Key facts.** `Randomized.PIT.map_evalVals`.
