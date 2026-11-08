<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterInstr.lean :: Complexity.UTab.CpS.regs_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distinct Source and Destination Registers

**Claim.** Let $M$ be a finite Turing machine with Boolean tape symbols, let $x$ be a finite Boolean string, and let $s$ be a copy-phase state for the tape length parameter $M.k$. Assign source and destination registers to $s$ by the specified copy-phase rules. Then its source and destination registers are distinct, and neither is register $10$.

**Proof.** Split into the constructors of the copy-phase state. In each case, the source and destination are fixed register indices determined by the constructor, and simplifying these definitions reduces the claims to inequalities between concrete elements of `Fin 11`. Those finite index inequalities are verified directly.
