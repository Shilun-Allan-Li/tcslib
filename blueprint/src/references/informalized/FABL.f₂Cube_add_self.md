<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPTesterExamples.lean :: FABL.f₂Cube_add_self -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Self-Sum in the Binary Cube

**Claim.** Every vector $x\in\mathbb{F}_2^n$ satisfies $x+x=0$.

**Proof.** Equality of vectors is determined coordinatewise. At each coordinate $i$, the entry of $x+x$ is $x_i+x_i$, which is zero because every element of $\mathbb{F}_2$ is its own additive inverse (`FABL.f₂_add_self`). Hence every coordinate is zero, so the vector sum is zero.

**Key facts.** `FABL.f₂_add_self`.
