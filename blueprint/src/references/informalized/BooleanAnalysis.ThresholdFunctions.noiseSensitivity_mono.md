<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/NoiseStability.lean :: BooleanAnalysis.ThresholdFunctions.noiseSensitivity_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Noise Sensitivity

**Claim.** If $\delta\le\delta'\le1/2$, then $\operatorname{NS}_{\delta}(f)\le\operatorname{NS}_{\delta'}(f)$.

**Proof.** The corresponding noise parameters satisfy $0\le1-2\delta'\le1-2\delta$. The stability formula expresses noise stability as $\sum_S \rho^{|S|}\widehat f(S)^2$ (\texttt{BooleanAnalysis.stability_formula}). For each subset $S$, raising nonnegative ordered parameters to the nonnegative integer power $|S|$ preserves their order; multiplying by the nonnegative square $\widehat f(S)^2$ does also. Summing termwise gives $\operatorname{Stab}_{1-2\delta'}(f)\le\operatorname{Stab}_{1-2\delta}(f)$. Since noise sensitivity is one half of one minus stability, this inequality reverses in the required way for the sensitivities.

**Key facts.** `BooleanAnalysis.stability_formula`.
