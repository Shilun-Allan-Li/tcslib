<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/ChiSquaredMGF.lean :: chi_squared_tail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-Sided Chi-Squared Concentration

**Claim.** For independent Gaussian coordinates with variance $1/k$, the probability that their squared norm differs from $1$ by more than $\varepsilon$ is at most $2\exp(-k\varepsilon^2/8)$, for $0<\varepsilon<1$.

**Proof.** For each coordinate define the centered summand $S_i=Y_i^2-1/k$. The Gaussian MGF estimate, packaged as the centered chi-squared Bernstein bound (\texttt{hasBernsteinMGF\_centered\_chi\_squared}), gives each $S_i$ Bernstein parameters $2/k^2$ and $k/4$. Independence and measurability are preserved under the coordinatewise map $y\mapsto y^2-1/k$. The independent-sum rule for Bernstein MGFs (\texttt{ProbabilityTheory.HasBernsteinMGF.sum\_of\_iIndepFun}) therefore gives the sum $\sum_i S_i$ parameters $2/k$ and $k/4$. Since $\sum_i S_i=\sum_iY_i^2-1$, the event in question is exactly the event that the absolute value of this sum exceeds $\varepsilon$. The two-sided Bernstein concentration bound (\texttt{ProbabilityTheory.HasBernsteinMGF.measure\_abs\_gt\_le}) applies: its range condition holds because $2(2/k)(k/4)=1$ and $\varepsilon<1$. It bounds the probability by $2\exp(-\varepsilon^2/(4(2/k)))$, which simplifies to $2\exp(-k\varepsilon^2/8)$.

**Key facts.** `centered_chi_squared_step`, `hasBernsteinMGF_centered_chi_squared`, `ProbabilityTheory.HasBernsteinMGF.sum_of_iIndepFun`, `ProbabilityTheory.HasBernsteinMGF.measure_abs_gt_le`.
