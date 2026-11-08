<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecRowOf_input_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Recovery from a Codec Row

**Claim.** If two configurations have equal input fields in their codec rows, then their Boolean input lists are equal.

**Proof.** The lists have the same length, namely $n$. To prove they agree, compare their entries at any index $i<n$. Evaluating the equality of input fields at the corresponding element of `Fin n` gives equality of the two default-indexed list values. Since $i$ lies within both lists, those values are the actual entries at index $i$. Thus the lists agree at every valid index, and extensionality for lists gives $x=y$.
