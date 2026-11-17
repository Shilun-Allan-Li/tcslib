<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Parse2.lean :: Complexity.LogProg.prefix_decomp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pairing decomposition at a separator

**Claim.** If the initial run of ones in $y$ has even length $r$, and the next two bits are false and true, then $y$ is the pairing of $r/2$ ones with the suffix after those separator bits.

**Proof.** Let $r$ be the length of the initial run of ones. Every position before $r$ contains a one (`Complexity.LogProg.getElem?_lt_tRun`), so the prefix of length $r$ is the unary string of $r$ ones; also, the run length is at most $y.length$ (`Complexity.LogProg.tRun_le`). The two hypotheses identify the next two entries as the separator false and true. Splitting the list at these positions therefore writes $y$ as that prefix, the separator, and the suffix beginning at $r+2$. Since $r$ is even, $2(r/2)=r$. The prefix is thus the doubled unary string of $r/2$ ones (`Complexity.LogProg.dbl_replicate`); expressing pairing as doubling followed by the separator (`Turing.pairEncode_eq_dbl`) gives the desired decomposition.

**Key facts.** `Complexity.LogProg.getElem?_lt_tRun`, `Complexity.LogProg.tRun_le`, `Complexity.LogProg.dbl_replicate`, `Turing.pairEncode_eq_dbl`.
