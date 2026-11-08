<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.coalitionalInfluence_eq_toward_add_toward -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Directional Influence Decomposition

**Claim.** For a Boolean function $f$ and coordinate set $J$, its coalitional influence on $J$ equals the sum of its coalitional influences toward $1$ and toward $-1$.

**Proof.** For each input $x$, the function can attain at least one of the two signs while changing coordinates in $J$: the unchanged input $x$ itself witnesses attainability of $f(x)$. Since $f(x)$ is either $1$ or $-1$, the two attainability events cannot both fail. Consequently, the sum of their indicator functions is one plus the indicator that both signs are attainable. Averaging over the uniform cube gives the sum of the two success probabilities as $1$ plus the coalitional influence. Also, the probabilities that $f$ equals $1$ and $-1$ sum to one (`FABL.uniformProbability_one_add_neg_one_eq_one`). Subtracting these two output probabilities from the corresponding success probabilities, as in the definition of directional influence, gives the claimed decomposition.

**Key facts.** `FABL.coalitionCanAttain_current`, `FABL.uniformProbability_one_add_neg_one_eq_one`.
