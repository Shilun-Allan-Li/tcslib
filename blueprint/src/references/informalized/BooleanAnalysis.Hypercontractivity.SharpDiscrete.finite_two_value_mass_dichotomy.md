<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/FiniteNoiseContraction.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.finite_two_value_mass_dichotomy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mass Dichotomy for Two-Valued Functions

**Claim.** If a function takes only the values $a$ and $b$, then it is constant at one of these values or the total weight $\gamma$ of the coordinates taking value $a$ lies between $\lambda$ and $1-\lambda$.

**Proof.** If the function is identically $a$ or identically $b$, one of the first two alternatives holds. Otherwise, choose a coordinate $i$ where its value is not $b$ and a coordinate $j$ where its value is not $a$. By the two-value hypothesis, $f_i=a$ and $f_j=b$. The weight $w_i$ is included in the sum defining $\gamma$, so positivity of all weights gives $\gamma\ge w_i\ge\lambda$. The complementary set of coordinates, where $f_k\ne a$, has total weight $1-\gamma$, since the two sets partition the finite index set and the total weight is one. It contains $j$, so $1-\gamma\ge w_j\ge\lambda$. Thus $\lambda\le\gamma\le1-\lambda$.
