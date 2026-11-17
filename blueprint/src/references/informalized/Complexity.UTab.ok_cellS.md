<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterInstr.lean :: Complexity.UTab.ok_cellS -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Validity of cell sources

**Claim.** Under the stated register hypotheses, every source in the cell-source list is valid for $\rho$.

**Proof.** Take a source in the cell-source list and split according to whether it comes from the fixed initial segment or from the appended past-position list. In the fixed segment, constant sources are valid by definition. Each conditional previous-cell source is valid by the validity criterion for such sources (`Complexity.UTab.ok_nbS`): when its condition holds, $t_0$ is false and the corresponding boundary flag is true, so the assumed lower bound on $\rho(r_Q)$ applies; when the condition fails, the source is constant false. The conditional current-cell sources are valid by the corresponding criterion (`Complexity.UTab.ok_chS`), using the hypothesis on $\rho(r_I)$ when the lower-bound flag is true. Finally, every appended past-position source is valid by the criterion for the past-position list (`Complexity.UTab.ok_psnS`), using the assumed lower bound on $\rho(r_{LB})$ when $t_0$ is false.

**Key facts.** `Complexity.UTab.ok_nbS`, `Complexity.UTab.ok_chS`, `Complexity.UTab.ok_psnS`.
