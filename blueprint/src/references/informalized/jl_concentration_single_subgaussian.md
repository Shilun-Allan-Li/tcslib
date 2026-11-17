<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/SubGaussian.lean :: jl_concentration_single_subgaussian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sub-Gaussian Squared-Norm Concentration

**Claim.** Under the stated measurability, independence, sub-Gaussian moment-generating-function bounds, and row second-moment identities, the probability that the squared norm of $Ax$ differs from $\|x\|^2$ by more than $s$ is at most $2\exp(-s^2/(4kc))$, provided $s$ is in the allowed Bernstein range.

**Proof.** Set $\sigma^2=\|x\|^2/k$, which is positive because $x\ne0$ and $k>0$. For each row projection, the sub-Gaussian-to-centered-square estimate (`subgaussian_centered_sq_bernstein`) shows that its centered square, $((Ax)_i)^2-\sigma^2$, satisfies the Bernstein moment-generating-function condition with parameters $c=2\sigma^4$ and $t_{\max}=1/(4\sigma^2)$. With the threshold $s=\varepsilon\|x\|^2$, the hypothesis $\varepsilon<1$ ensures $s\le 2kc t_{\max}$: indeed, for these parameters, $2kc t_{\max}=\|x\|^2$. Apply the Bernstein-based concentration theorem (`jl_concentration_single_via_bernstein`). Its deviation event is the desired one because the squared norm of a Euclidean vector is the sum of its coordinate squares (`norm_sq_toEuclideanLin`), and $k(\|x\|^2/k)=\|x\|^2$. Finally, substituting $s=\varepsilon\|x\|^2$ and $c=2(\|x\|^2/k)^2$ into the exponent gives $-s^2/(4kc)=-k\varepsilon^2/8$.

**Key facts.** `subgaussian_centered_sq_bernstein`, `jl_concentration_single_via_bernstein`, `norm_sq_toEuclideanLin`.
