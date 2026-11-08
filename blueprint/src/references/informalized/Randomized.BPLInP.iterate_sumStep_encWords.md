<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInPWords.lean :: Randomized.BPLInP.iterate_sumStep_encWords -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Summing an Encoded List

**Claim.** For every finite list $L$ of natural numbers and every $a\in\mathbb N$, applying the sum update $|L|$ times to the pairing of the binary representation of $a$ with the encoded list of binary representations of the entries of $L$ yields the pairing of the binary representation of $a+\sum_{n\in L}n$ with the empty bit string.

**Proof.** Induct on the list $L$, generalizing the initial accumulator $a$. If $L$ is empty, no updates are needed, its encoding is empty, and its sum is zero. For the cons case, write $L=n::L'$. The encoded list separates into the encoding of the binary representation of $n$ followed by the encoding of the remaining entries; `encWords_cons` gives this decomposition. One sum update on the first encoded entry changes the accumulator from $a$ to $a+n$, since binary representations decode to their values by `bitsVal_bits`, and leaves the encoding of $L'$ as the remaining input. Apply the induction hypothesis to $L'$ with accumulator $a+n$. The list-sum decomposition and associativity of addition identify the resulting accumulator with $a+\sum_{m\in L}m$, and the remaining encoded list is empty.

**Key facts.** `Complexity.BinArith.encWords_cons`, `Complexity.LogProg.bitsVal_bits`.
