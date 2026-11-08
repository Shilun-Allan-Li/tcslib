<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/SubGaussian.lean :: subgaussian_centered_sq_bernstein -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Centered square Bernstein bound

**Claim.** Under the stated sub-gaussian and second-moment hypotheses, the centered square $Z^2-\sigma^2$ has an MGF bound with parameters $2\sigma^4$ and $1/(4\sigma^2)$.

**Proof.** Fix $t$ with $|t|\le 1/(4\sigma^2)$. The absolute-value inequality gives both $-1/(4\sigma^2)\le t$ and $t\le 1/(4\sigma^2)$. If $t\ge0$, apply the nonnegative-parameter centered-square bound (`mgf_centered_sq_le_of_nonneg`); if $t<0$, apply its nonpositive-parameter counterpart (`mgf_centered_sq_le_of_nonpos`), using the second-moment identity in that case. Each gives integrability of the exponential and the bound $\operatorname{mgf}_{Z^2-\sigma^2}(t)\le \exp(2\sigma^4t^2)$. Since these conclusions hold for every such $t$, they are exactly the two requirements in the definition of the asserted Bernstein MGF property.

**Key facts.** `mgf_centered_sq_le_of_nonneg`, `mgf_centered_sq_le_of_nonpos`.
