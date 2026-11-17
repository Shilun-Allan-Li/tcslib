<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Parity.lean :: BoolCircuit.xorNode_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of one XOR step

**Claim.** If each input pair consists of circuits evaluating to complementary values, then the first circuit produced by one XOR step evaluates to the exclusive OR of the first circuits in the two input pairs.

**Proof.** Let the first circuits in the two pairs evaluate to $a$ and $b$. By the hypotheses, their partners evaluate to $\neg a$ and $\neg b$. The first output circuit is the disjunction of the conjunctions $a\wedge\neg b$ and $\neg a\wedge b$. This is true precisely when $a$ and $b$ differ, which is exactly $a\mathbin{\mathrm{xor}}b$.
