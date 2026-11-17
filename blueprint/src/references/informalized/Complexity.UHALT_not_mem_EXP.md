<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UHaltMachine.lean :: Complexity.UHALT_not_mem_EXP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Universal Halting Is Outside Exponential Time

**Claim.** For every effective machine representation scheme $c$, the unary language of numbers whose binary expansions begin with $1s$, where $s$ encodes an advice string and an input on which the machine decoded from that advice halts, is not in $\mathrm{EXP}=\bigcup_{d\in\mathbb{N}}\mathrm{DTIME}(2^{n^d})$.

**Proof.** Suppose the language belonged to the displayed union. Membership in a union supplies some exponent $k$ for which it belongs to the corresponding time class $\mathrm{DTIME}(2^{n^k})$. But `UHALT_not_mem_DTIME` excludes membership in $\mathrm{DTIME}(T)$ for every time-bound function $T$, including $T(n)=2^{n^k}$. This contradiction proves the claim.

**Key facts.** `Complexity.UHALT_not_mem_DTIME`.
