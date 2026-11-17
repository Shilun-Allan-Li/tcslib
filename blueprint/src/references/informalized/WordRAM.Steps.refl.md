<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.Steps.refl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-Step Reflexivity

**Claim.** For any word size, program, and configuration $c$, zero steps of the program take $c$ to itself.

**Proof.** By the definition of a zero-step run, this assertion is exactly the equality of the initial and final configurations. Taking both to be $c$ gives the result by reflexivity of equality.
