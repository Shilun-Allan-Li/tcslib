<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ArrowTheorem.lean :: ArrowTheorem.degree_one_implies_dictator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree-One Fourier Support Forces a Dictator

**Claim.** If a 7-valued Boolean function has all Fourier coefficients outside degree one equal to zero and is unanimous, then it is a dictator.

**Proof.** By the Walsh expansion and the vanishing of every coefficient except those indexed by singletons, for every input $x$ we have $f(x)=\sum_i a_i\,\mathrm{boolToSign}(x_i)$, where $a_i=\widehat f(\{i\})$. At the all-false input every sign is $1$, so unanimity gives $\sum_i a_i=1$. Now fix $i$ and take the input whose only true coordinate is $i$. Its Walsh expansion is $-a_i+\sum_{j\ne i}a_j=1-2a_i$. Since the function takes only the values $1$ and $-1$, this forces $a_i$ to be either $0$ or $1$. Let $J$ be the set of indices with $a_i=1$. The coefficients outside $J$ vanish, while those in $J$ equal one, so $|J|=\sum_i a_i=1$. Thus there is a unique $j_0$ with coefficient one; all other coefficients are zero. Substituting these coefficients into the Walsh expansion yields $f(x)=\mathrm{boolToSign}(x_{j_0})$ for every $x$, which is precisely the dictator at $j_0$.

**Key facts.** `BooleanAnalysis.walsh_expansion`, `BooleanAnalysis.chiS_singleton`, `BooleanAnalysis.dictator_eq_chi`.
