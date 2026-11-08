<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ZeroSpace.lean :: Turing.FinTM.ComputesInSpace.k_eq_zero_of_exists_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Space Bound Forces No Work Tapes

**Claim.** If the space bound is zero at some input length and the machine computes under that bound on every input, then the machine has no work tapes.

**Proof.** Choose $n$ with $s(n)=0$ and run the machine on the Boolean word consisting of $n$ copies of false. The hypothesis supplies a time at which its space use is at most $s(n)=0$. For every machine and input, the number of work tapes is at most the space used (`k_le_spaceUsed`). Thus $M.k\leq 0$, and since the number of work tapes is a natural number, $M.k=0$.

**Key facts.** `Turing.FinTM.k_le_spaceUsed`.
