<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitLoop_result -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output of the split search loop

**Claim.** The word encoded from the prefix and suffix cut at the first accepted split-step iterate, or the empty word if no iterate is accepted, equals the corresponding encoding cut at the index returned by the arithmetic split search, again using the empty word when the search fails.

**Proof.** The orbit-search equality identifies the first accepted iterate index with the result of the arithmetic search. If that search returns no index, both expressions are empty. If it returns an index $i$, membership of $i$ in the search range gives $i\le |w|$. The split-step orbit at index $i$ is the word of $i$ copies of $1$, hence has length $i$. Consequently, both expressions encode the prefix of $w$ of length $i$ together with the suffix after that prefix.

**Key facts.** `Turing.FinTM.splitFind_eq`, `Turing.FinTM.splitStep_orbit`.
