<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Classes.lean :: Randomized.exists_ofFn_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Function Representation of a List

**Claim.** Every Boolean list of length $m$ is the list associated with some function from the indices $0,\ldots,m-1$ to the Booleans.

**Proof.** Define the function at index $i$ to be the entry of the list at position $i$. The length hypothesis ensures that every such index is within the list. The two lists have the same length, and at each position below that length their entries agree by construction. Hence the lists are equal.
