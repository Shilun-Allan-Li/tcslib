<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UHaltMachine.lean :: Complexity.UHALT_not_mem_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Universal Halting Is Not Polynomial Time

**Claim.** For every effective machine representation scheme $c$, the unary language of numbers whose binary expansions begin with $1s$, where $s$ encodes an advice string and an input on which the machine decoded from that advice halts, is not decidable in time $n^d+1$ up to a constant factor for any natural number $d$.

**Proof.** Assume the language belongs to polynomial time. The containment theorem `P_subset_EXP` then places it in exponential time. This contradicts `UHALT_not_mem_EXP`, which says that universal halting is outside exponential time. Therefore it is not in polynomial time.

**Key facts.** `Complexity.P_subset_EXP`, `Complexity.UHALT_not_mem_EXP`.
