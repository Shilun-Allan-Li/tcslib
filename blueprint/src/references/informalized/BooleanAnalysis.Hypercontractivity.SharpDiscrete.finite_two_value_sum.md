<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/FiniteNoiseContraction.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.finite_two_value_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weighted Sum of a Two-Valued Function

**Claim.** If $f$ takes only values $a$ and $b$ and the weights sum to one, then the weighted sum of $\varphi(f_i)$ equals $\gamma\varphi(a)+(1-\gamma)\varphi(b)$, where $\gamma$ is the total weight on coordinates with value $a$.

**Proof.** Partition the indices into those with $f_i=a$ and those with $f_i\ne a$. On the first set, the summand is $w_i\varphi(a)$; on the second, the two-value hypothesis forces $f_i=b$, so it is $w_i\varphi(b)$. The first set has weight $\gamma$. The second has weight $1-\gamma$, since the two sets partition the indices and the total weight is one. Adding the two contributions gives the identity.
