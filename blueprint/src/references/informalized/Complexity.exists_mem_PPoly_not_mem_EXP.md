<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UHaltMachine.lean :: Complexity.exists_mem_PPoly_not_mem_EXP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial circuits exceed exponential time

**Claim.** Some language of binary strings has polynomial-size Boolean circuits but is not decidable by any deterministic finite Turing machine within any bound c·2^{n^d}.

**Proof.** Take an effective machine code c, whose existence is supplied by `exists_effectiveMachineCode`, and consider the universal halting language UHALT associated with its machine code. The theorem `UHALT_mem_PPoly` gives polynomial-size circuit families deciding this language. The diagonalization theorem `UHALT_not_mem_EXP` says that this same language is not in EXP. By the definition of EXP as the union of deterministic time classes with bounds 2^{n^d}, this gives the claimed separation.

**Key facts.** `Turing.exists_effectiveMachineCode`, `Complexity.UHALT_mem_PPoly`, `Complexity.UHALT_not_mem_EXP`.
