<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Perturbation.lean :: BooleanAnalysis.GaussianSpace.Invariance.integrable_lipschitz_comp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability Under Lipschitz Composition

**Claim.** If $U$ is integrable on a finite measure space and $\psi$ is Lipschitz, then $\psi\circ U$ is integrable.

**Proof.** Subtract the constant value $\psi(0)$ from $\psi$. The resulting function remains Lipschitz with the same constant and vanishes at zero. The Lipschitz composition estimate therefore makes its composition with $U$ an $L^1$ function: the input is in $L^1$, and the pointwise bound by a constant multiple of $|U|$ controls the output. Hence $\psi(U)-\psi(0)$ is integrable. Adding back the constant function preserves integrability on a finite measure space, proving the claim.
