<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterInstr.lean :: Complexity.UTab.ok_inpS -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Validity of input sources

**Claim.** Under the stated register hypotheses, if the chosen layer source is valid, then every source in the input-source list is valid for $\rho$.

**Proof.** Take a source in the input list and split between its fixed initial segment and its appended past-position list. In the fixed segment, the constant sources are valid by definition, and the chosen layer source is valid by hypothesis. The conditional previous-cell sources are valid by `Complexity.UTab.ok_nbS`: whenever their conditions hold, the relevant conjunction forces $t_0$ and $p_0$ to be false, so the assumed lower bound on $\rho(r_Q)$ applies. The conditional current-cell sources are valid by `Complexity.UTab.ok_chS`, using the lower bound on $\rho(r_I)$ when $p_0$ is false. The appended past-position sources are valid by `Complexity.UTab.ok_psnS`, using the lower bound on $\rho(r_{LB})$ when $t_0$ is false.

**Key facts.** `Complexity.UTab.ok_nbS`, `Complexity.UTab.ok_chS`, `Complexity.UTab.ok_psnS`.
