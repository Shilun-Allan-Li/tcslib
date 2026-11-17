<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomBits.lean :: Randomized.bitsVal_ofFn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positional Bit Expansion

**Claim.** For every natural number $L$ and bit string $f : \mathrm{Fin}(L) \to \{0,1\}$, the value of the list of its bits, with the first entry least significant, is $\sum_{j=0}^{L-1} f(j)2^j$.

**Proof.** Induct on $L$. For $L=0$, the list and the sum are both empty, so both sides are zero. For the step from $L$ to $L+1$, the list is the first bit followed by the list of the remaining bits. By the induction hypothesis, the latter list has value the sum of the remaining bits weighted by their powers of two. The recursive definition of the list value doubles that remaining value and adds the first bit. Splitting the sum into its first term and the remaining terms gives the same expression: the first term has weight $2^0=1$, and each later bit's exponent increases by one, supplying exactly the factor of two.
