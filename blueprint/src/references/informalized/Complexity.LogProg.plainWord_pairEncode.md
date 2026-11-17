<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARM.lean :: Complexity.LogProg.plainWord_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovery of the paired payload

**Claim.** Pairing the unary string of $n$ ones with $w$ and then removing the initial run of ones and the two separator bits recovers $w$.

**Proof.** The initial run of ones in this encoding has length $2n$ (`Complexity.LogProg.tRun_pairEncode`): doubling the unary string gives $2n$ ones, followed by the separator beginning with false. Thus dropping the run and the next two separator bits amounts to dropping the first $2n+2$ entries. By the paired-encoding decomposition (`Turing.pairEncode_eq_dbl`) and the doubled-replicate identity (`Complexity.LogProg.dbl_replicate`), the encoding is a block of $2n$ ones followed by the two separator bits and $w$. Removing that prefix leaves exactly $w$.

**Key facts.** `Complexity.LogProg.tRun_pairEncode`, `Turing.pairEncode_eq_dbl`, `Complexity.LogProg.dbl_replicate`.
