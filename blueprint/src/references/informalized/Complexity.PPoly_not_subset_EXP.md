<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UHaltMachine.lean :: Complexity.PPoly_not_subset_EXP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial circuits exceed exponential time

**Claim.** There is a language recognized by a polynomial-size, fan-in-two circuit family that is not in exponential time.

**Proof.** Use the existence theorem that supplies a language $L$ in the polynomial-circuit class but outside $	extsf{EXP}$ (`Complexity.exists_mem_PPoly_not_mem_EXP`). If polynomial-circuit languages were a subset of $	extsf{EXP}$, applying that inclusion to $L$ would put $L$ in $	extsf{EXP}$, contradicting the theorem’s choice of $L$.

**Key facts.** `Complexity.exists_mem_PPoly_not_mem_EXP`.
