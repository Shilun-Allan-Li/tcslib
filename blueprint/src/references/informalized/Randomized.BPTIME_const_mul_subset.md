<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTM.lean :: Randomized.BPTIME_const_mul_subset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constant scaling of randomized time

**Claim.** For every natural number $a$ and time bound $T$, every language in $\mathrm{BPTIME}(n\mapsto aT(n))$ belongs to $\mathrm{BPTIME}(T)$.

**Proof.** Choose a witnessing machine and constant $c$ for membership in the first class. Keep the same machine and use the constant $ca$ for the time bound $T$. Associativity of multiplication gives $c(aT(n))=(ca)T(n)$ for every input length, so the original halting and success guarantees apply unchanged.
