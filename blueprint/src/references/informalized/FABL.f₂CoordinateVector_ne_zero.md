<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPTesterExamples.lean :: FABL.f₂CoordinateVector_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate vectors are nonzero

**Claim.** Every standard coordinate vector in $\mathbb{F}_2^n$ is nonzero.

**Proof.** If the vector indexed by $i$ were zero, its value at coordinate $i$ would be zero. But by the definition of the standard coordinate vector, that coordinate equals $1$. Since $1\ne0$ in $\mathbb{F}_2$, this is impossible.
