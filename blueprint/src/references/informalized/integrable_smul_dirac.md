<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Rademacher.lean :: integrable_smul_dirac -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability under a scaled Dirac measure

**Claim.** For any point $a\in\mathbb R$, every real-valued function is integrable with respect to $\tfrac12\delta_a$.

**Proof.** A real-valued function is integrable with respect to the Dirac measure at $a$, because that measure is concentrated at a point where the function has a finite real value. Scaling this measure by the finite mass $1/2$ preserves integrability. The finiteness needed for this scaling is precisely that $1/2$ is not infinite (rad_half_ne_top).

**Key facts.** `rad_half_ne_top`.
