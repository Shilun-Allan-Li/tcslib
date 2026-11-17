<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.effect_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Effect of Writing One

**Claim.** Executing the instruction that writes one at address $i$ updates the memory at $i$ with the $W$-bit encoding of $1$.

**Proof.** The definition of the effect of this instruction is precisely the function update that replaces the value at address $i$ by the encoding of $1$.
