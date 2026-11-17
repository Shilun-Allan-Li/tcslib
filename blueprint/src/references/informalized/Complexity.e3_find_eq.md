<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.e3_find_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Orbit Search and Split Search

**Claim.** The search over indices from $0$ through $|w|$ for the first state passing the round test returns the same optional index as the bounded split search at length $|w|$.

**Proof.** Replace the round-test predicate on each index in the range by the predicate defining the split search. The search-congruence principle says this pointwise replacement does not change the first match (`Complexity.e3_find_congr`). For each such index $i$, we have $i\le |w|$, so the orbit lemma identifies the state after $i$ steps with the word of $i$ true bits (`Complexity.e3_step_orbit`). Its length is therefore $i$, and the round test is exactly $i+C\cdot 2^{(i+1)^c}=|w|$. Thus the two searches use the same predicate on the same range and return the same result.

**Key facts.** `Complexity.e3_find_congr`, `Complexity.e3_step_orbit`.
