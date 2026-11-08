<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.comp_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logspace Membership of the Constructed Language

**Claim.** Under the stated polynomial output-length bound and logspace decidability assumptions for the output bits and output length, the constructed language belongs to LOGSPACE in either Boolean mode.

**Proof.** Use the four-query bank consisting of the input-bit test, the input-length test, and the two lifted tests that recover an output bit or check the output length. By the hypotheses defining implicit logspace computability, each bank language is in LOGSPACE (`Complexity.compBank_mem`). The counter program `compARM` simulates the required parsing and index checks, then uses the appropriate lifted query according to the mode. Its run is correct and satisfies the polynomial register bound established by `comp_run`. Applying the general theorem that a counter program with logspace query languages and a polynomially bounded, correct halting run decides a LOGSPACE language (`Complexity.LogProg.arm_decides_poly`) yields the claimed membership. The constants supplied to that theorem are the program's register-bound parameters.

**Key facts.** `Complexity.compBank_mem`, `Complexity.comp_run`, `Complexity.LogProg.arm_decides_poly`.
