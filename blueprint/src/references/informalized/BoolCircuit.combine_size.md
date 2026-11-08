<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeNCAC.lean :: BoolCircuit.combine_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size of a Combined Circuit

**Claim.** For any list of Boolean circuit trees, combining the list produces a circuit whose size is at most the sum of their sizes, plus the length of the list and one.

**Proof.** The fuel induction considers four cases. With zero fuel, the result is a single node over the original list, so its size is one plus the sum of the sizes of the listed circuits; this is within the stated bound. With positive fuel and an empty list, the result is an empty node, and the inequality follows directly. With positive fuel and a singleton list, the result is that sole circuit, whose size is bounded by the claimed expression. For a list with at least two entries, the induction hypothesis bounds the size of the recursive combination of the paired list. Pairing preserves the total size of the original circuits and does not increase the list length, as expressed by the pair-up size bound (`BoolCircuit.sumSize_pairUp`). Combining these facts gives the required inequality.

**Key facts.** `BoolCircuit.combineFuel_size`.
