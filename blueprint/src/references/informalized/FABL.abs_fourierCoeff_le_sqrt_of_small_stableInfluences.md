<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.abs_fourierCoeff_le_sqrt_of_small_stableInfluences -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficient bound from stable influence

**Claim.** If $0\leq\varepsilon<1$ and all stable influences at parameter $1-\varepsilon$ are at most $\varepsilon$, then for every nonempty coordinate set $S$ of size at most $t$, $|\widehat f(S)|\leq\sqrt{\varepsilon/(1-\varepsilon)^{t-1}}$.

**Proof.** Choose a coordinate $i\in S$. Since $0<1-\varepsilon\leq1$ and $|S|\leq t$, the power $(1-\varepsilon)^{t-1}$ is at most $(1-\varepsilon)^{|S|-1}$. The term indexed by $S$ occurs among the nonnegative summands defining the stable influence at $i$, so $(1-\varepsilon)^{|S|-1}\widehat f(S)^2\leq \operatorname{Inf}^{(1-\varepsilon)}_i[f]$. The assumed influence bound therefore gives $(1-\varepsilon)^{t-1}\widehat f(S)^2\leq\varepsilon$. Dividing by the positive factor $(1-\varepsilon)^{t-1}$ and taking square roots yields the claimed estimate.
