<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/StartUp.lean :: Light.Compiler.agreeOutside_poolCode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Memory preserved outside the pool

**Claim.** Executing the pool-initialization program changes memory only at pool addresses with indices from $0$ through $N$.

**Proof.** The first instruction writes to the pool cell at index $0$, which belongs to the pool. Every subsequent instruction is indexed by some $n<N$ and writes to the cell at index $n+1$, which is at most $N$ and hence also belongs to the pool. Therefore all writes lie in the pool, and the preservation principle for instruction lists implies that memory agrees with its initial value outside the pool (\texttt{WordRAM.agreeOutside_effects}).

**Key facts.** `WordRAM.agreeOutside_effects`.
