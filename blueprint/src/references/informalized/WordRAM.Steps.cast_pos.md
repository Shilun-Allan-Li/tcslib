<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.Steps.cast_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Changing the Final Program Counter

**Claim.** If $n$ steps take $c$ to the configuration with program counter $p$ and memory $m$, and $p=p'$, then $n$ steps take $c$ to the configuration with program counter $p'$ and memory $m$.

**Proof.** Substitute $p'$ for $p$ in the endpoint configuration using the given equality. The step-sequence relation is then exactly the claimed one.
