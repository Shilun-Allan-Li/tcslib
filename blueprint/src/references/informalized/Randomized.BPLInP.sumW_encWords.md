<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInPWords.lean :: Randomized.BPLInP.sumW_encWords -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding the sum of encoded words

**Claim.** For every finite list $L$ of natural numbers, applying the summing operation to the concatenation of the encodings of their binary expansions returns the binary expansion of $\sum_{m\in L}m$.

**Proof.** Let $r$ be the number of iterations used in the definition of the summing operation. The encoded word list has length at least $2|L|$ by the length bound for encoded words (`Randomized.BPLInP.two_mul_length_le_encWords`), so in particular $|L|\le r$. Write $r=|L|+d$ for some $d\ge0$. The iteration formula for `sumStep` says that after $|L|$ steps the state is the encoding of the accumulated sum and an empty remainder (`Randomized.BPLInP.iterate_sumStep_encWords`); here the initial accumulator is zero. The encoding of the binary expansion of zero is empty, so the initial state is exactly the one required by that formula. The resulting encoded sum is fixed by one further `sumStep`: decoding its first component recovers the binary word, decoding the empty second component gives zero, and the binary-value identity `bitsVal (Nat.bits n)=n` (`Complexity.LogProg.bitsVal_bits`) makes the addition return the same number. Hence all $d$ remaining iterations leave this encoding unchanged. Finally, decoding the first component of an encoded pair returns that component (`Complexity.pairFstD_pairEncode`), yielding the binary expansion of $L.sum$.

**Key facts.** `Randomized.BPLInP.two_mul_length_le_encWords`, `Randomized.BPLInP.iterate_sumStep_encWords`, `Complexity.LogProg.bitsVal_bits`, `Complexity.pairFstD_pairEncode`.
