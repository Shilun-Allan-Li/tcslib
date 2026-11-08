<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/NCAC.lean :: BoolCircuit.polylog_add_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polylogarithmic bound after adding one

**Claim.** For natural numbers $b,d,L,t$, if $t\le b(L+1)^d$, then $t+1\le(b+1)(L+1)^d$.

**Proof.** Because $L+1\ge1$, its $d$th power is at least $1$. Adding this bound to the assumed inequality gives $t+1\le b(L+1)^d+(L+1)^d=(b+1)(L+1)^d$.
