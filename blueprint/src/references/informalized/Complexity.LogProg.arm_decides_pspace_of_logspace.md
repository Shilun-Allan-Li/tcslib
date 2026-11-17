<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMWidth.lean :: Complexity.LogProg.arm_decides_pspace_of_logspace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logspace oracles in polynomial space

**Claim.** If the register computation has polynomially bounded register words and is correct and halting on every input, then logarithmic-space oracle languages suffice to decide $L$ in polynomial space.

**Proof.** Each oracle language in logarithmic space is also in polynomial space (`LOGSPACE_subset_PSPACE`). Apply the polynomial-space register-program theorem (`arm_decides_pspace`) to the same computation and its given polynomial bound on register-word lengths. It follows that $L\in\mathrm{PSPACE}$.

**Key facts.** `Complexity.LOGSPACE_subset_PSPACE`, `Complexity.LogProg.arm_decides_pspace`.
