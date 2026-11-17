<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInPWords.lean :: Randomized.BPLInP.iterate_sumStep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Iterated Sum Update

**Claim.** For every $a,i\in\mathbb N$ and bit string $w$, applying the sum update $i$ times to the pairing of the binary representation of $a$ with $w$ yields the pairing of the binary representation of $a+\sum_{j=0}^{i-1}\mathrm{val}(\pi_1(\pi_2^{[j]}(w)))$ with $\pi_2^{[i]}(w)$.

**Proof.** Induct on the number $i$ of updates. When $i=0$, the sum is empty and the second component is still $w$, so the formula follows immediately. For the successor step, apply one more sum update to the induction hypothesis. This update adds to the accumulated binary value the value encoded by the first projection of the current second component, and replaces that component by its second projection. The binary representation decodes to its natural number by `bitsVal_bits`; the sum over the first $i+1$ indices splits into the first $i$ terms and the new term. Associativity of addition aligns these two descriptions, yielding the formula at $i+1$.

**Key facts.** `Complexity.LogProg.bitsVal_bits`.
