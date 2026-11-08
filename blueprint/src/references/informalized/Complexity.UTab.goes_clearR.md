<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterLayer.lean :: Complexity.UTab.goes_clearR -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register clearing loop

**Claim.** Starting from mode $s$ and register values $e.f$, the program reaches the exit mode with register $s.reg$ set to zero, every other register unchanged, the input position still $p$, and the output unchanged, within $2e.f(s.reg)+1$ steps.

**Proof.** The loop-clearing result states that for any register assignment $\rho$, the program starting at the clearing-loop entry reaches the exit with register assignment $\operatorname{update}(\rho,s.reg,0)$, leaves the input position and output unchanged, and takes at most $2\rho(s.reg)+1$ steps (`goes_clear`). Apply it with $\rho=e.f$. The register-update identity says that updating $e.f$ at $s.reg$ to zero is exactly the register assignment represented by setting that field of $e$ to zero (`ER.update_f`). Substituting this identity gives the claimed endpoint and bound.

**Key facts.** `Complexity.UTab.goes_clear`, `Complexity.UTab.ER.update_f`.
