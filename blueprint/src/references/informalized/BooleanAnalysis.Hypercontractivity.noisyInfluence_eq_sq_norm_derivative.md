<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/Influence.lean :: BooleanAnalysis.Hypercontractivity.noisyInfluence_eq_sq_norm_derivative -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noisy Influence as a Derivative Norm

**Claim.** For $\rho\ge0$, the noisy influence of $f$ at coordinate $i$ equals the square of the $L^2$ norm of $T_{\sqrt{\rho}}D_i f$.

**Proof.** Square the norm using its definition and the nonnegativity of $\langle g,g\rangle$ (`BooleanAnalysis.innerProduct_self_nonneg`), so that the square root in the norm contributes exactly this inner product. Self-adjointness of the noise operator (`BooleanAnalysis.noiseOp_self_adjoint`) moves one noise operator across the inner product, and the composition law (`BooleanAnalysis.noiseOp_compose`) combines the two operators into noise with parameter $\rho$, since $(\sqrt{\rho})^2=\rho$. The stability formula (`BooleanAnalysis.stability_formula`) then writes the result as the sum of $\rho^{|S|}\widehat{D_i f}(S)^2$. The derivative coefficient formula (`BooleanAnalysis.Hypercontractivity.fourierCoeff_derivative`) makes terms with $i\in S$ vanish and identifies each remaining coefficient with $\widehat f(S\cup\{i\})$. Finally, reindex the sum by adjoining $i$ to each subset not containing it. This is a bijection with subsets containing $i$; the new subset has cardinality one larger, so its weight $\rho^{|S|}$ is precisely the noisy-influence weight $\rho^{|S\cup\{i\}|-1}$. The resulting sum is the definition of the noisy influence.

**Key facts.** `BooleanAnalysis.innerProduct_self_nonneg`, `BooleanAnalysis.noiseOp_self_adjoint`, `BooleanAnalysis.noiseOp_compose`, `BooleanAnalysis.stability_formula`, `BooleanAnalysis.Hypercontractivity.fourierCoeff_derivative`.
