<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Parity.lean :: BoolCircuit.pairFanin_xorPairUp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pairwise XOR fanin bound

**Claim.** For every finite list of pairs of circuits, the pair fanin after applying the pairwise XOR construction is at most the maximum of $2$ and the original pair fanin.

**Proof.** Proceed by the list cases in the definition of the construction. The empty list produces the empty list, whose pair fanin is $0$. A singleton list is unchanged, so its pair fanin is the original pair fanin, which is bounded by its maximum with $2$. For a list with at least two entries, the construction makes an XOR pair from the first two pairs and recursively processes the remaining list. By the XOR pair fanin bound (`BoolCircuit.pairFanin_xorNode`), the new head's fanin is at most $2$ or the maximum fanin of the first two input pairs. By induction, the tail's pair fanin is at most the maximum of $2$ and the original tail's pair fanin. The pair fanin recursion (`BoolCircuit.pairFanin_cons`) combines these bounds; since both first input fanins and the tail fanin are bounded by the original list's pair fanin, the result is at most the maximum of $2$ and that original pair fanin.

**Key facts.** `BoolCircuit.pairFanin_cons`, `BoolCircuit.pairFanin_xorNode`.
