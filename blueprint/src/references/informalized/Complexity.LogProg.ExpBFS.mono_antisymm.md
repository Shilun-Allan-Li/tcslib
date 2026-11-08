<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Relax.lean :: Complexity.LogProg.ExpBFS.mono_antisymm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Antisymmetry of Memory Inclusion

**Claim.** If each integer where $M$ is true is also one where $M'$ is true, and conversely, then $M'=M$.

**Proof.** To show the two Boolean-valued functions are equal, fix any integer $z$. The two inclusion hypotheses apply at this point. If $M(z)$ is true, the first inclusion forces $M'(z)$ to be true; if $M'(z)$ is true, the reverse inclusion forces $M(z)$ to be true. Hence the two Boolean values agree in every case, so the functions are equal pointwise and therefore equal.
