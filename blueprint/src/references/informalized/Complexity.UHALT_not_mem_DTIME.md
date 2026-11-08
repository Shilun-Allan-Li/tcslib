<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UHaltMachine.lean :: Complexity.UHALT_not_mem_DTIME -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Universal Halting Exceeds Every Time Bound

**Claim.** Let $c$ be an effective machine representation scheme, and let $T\colon\mathbb{N}\to\mathbb{N}$ be any function. The unary language of numbers whose binary expansions begin with $1s$, where $s$ encodes an advice string and an input on which the machine decoded from that advice halts, is not decidable by a finite binary Turing machine in time bounded by any constant multiple of $T$.

**Proof.** Assume, for contradiction, that the language belongs to $\mathrm{DTIME}(T)$. By the definition of this class, there are a constant and a finite binary Turing machine deciding the language within that constant multiple of $T$. The theorem `not_decidesInTime_UHALT` rules out every such decider for universal halting, so this assumption is impossible.

**Key facts.** `Complexity.not_decidesInTime_UHALT`.
