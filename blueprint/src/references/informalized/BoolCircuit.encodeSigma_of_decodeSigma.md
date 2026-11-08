<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Encoding.lean :: BoolCircuit.encodeSigma_of_decodeSigma -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding After Successful Decoding

**Claim.** For any Boolean list $bs$ and any pair consisting of a natural number $n$ and a tree circuit on $n$ variables, if decoding $bs$ succeeds and returns that pair, then encoding the pair gives $bs$.

**Proof.** Unfold the decoder and consider its successive cases. If decoding the initial natural-number code fails, the decoder returns none, contradicting the hypothesis that it returned the given pair. Otherwise, let the decoded number be $n$ and the remaining list be $r$. The next check reads a circuit from $r$ and requires that its remaining suffix be empty; failure of the circuit read, or a nonempty suffix, again makes the decoder return none. In the successful case, the decoder has obtained a circuit $C'$ and additionally checked that encoding the pair $(n,C')$ equals the original list $bs$. Its returned value is that same pair, so equality of the returned pair with the given pair identifies the given circuit and index with $C'$ and $n$. The checked encoding equality is therefore exactly the desired conclusion.
