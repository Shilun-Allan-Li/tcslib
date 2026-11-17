<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/AddSub.lean :: Complexity.BinArith.le_mem_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Comparison Is in P

**Claim.** The language of inputs whose parsed first numeral has value at most that of the parsed second numeral belongs to $P$.

**Proof.** The comparison predicate is polynomial-time computable: `polyTimeComputable_le` supplies a polynomial-time procedure that outputs the Boolean value of the predicate. The general test-to-language result, `mem_P_of_test`, says that the set of inputs on which any such Boolean test returns true belongs to $P$. Applying it to this comparison test gives the claim.

**Key facts.** `Complexity.BinArith.polyTimeComputable_le`, `Complexity.mem_P_of_test`.
