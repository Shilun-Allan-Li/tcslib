<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.AgreeOutside.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement outside a larger set

**Claim.** If $s\subseteq t$ and two memories agree outside $s$, then they agree outside $t$.

**Proof.** Every address outside $t$ is also outside $s$: taking complements reverses the inclusion $s\subseteq t$. The original agreement therefore applies at every address outside $t$, proving the claim.
