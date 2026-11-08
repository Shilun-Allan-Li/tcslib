<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.BoundedCubeFunction.noise_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the noise operator

**Claim.** Applying the noise operator with parameter $\rho\in[-1,1]$ to a bounded cube function and evaluating at $x$ gives the noise-kernel expectation of that function at $x$.

**Proof.** The noise operation on a bounded cube function is defined to have underlying function $x\mapsto (T_\rho f)(x)$, where $T_\rho$ is the noise operator. Evaluating this underlying function at $x$ therefore gives $(T_\rho f)(x)$ directly.
