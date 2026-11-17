<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.effects_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Effect of the Empty Instruction List

**Claim.** Applying the empty instruction list leaves any memory $m$ unchanged.

**Proof.** The effect of a list is a fold over its instructions, starting from the input memory. The empty list performs no instruction effects, so the fold returns its initial memory $m$.
