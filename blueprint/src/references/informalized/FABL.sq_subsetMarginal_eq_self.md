<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.sq_subsetMarginal_eq_self -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Squared Marginal Difference

**Claim.** For a monotone function on subsets taking only the values $0$ and $1$, the square of $f(S\cup\{i\})-f(S\setminus\{i\})$ equals that difference.

**Proof.** The set $S\setminus\{i\}$ is contained in $S\cup\{i\}$, so monotonicity gives $f(S\setminus\{i\})\le f(S\cup\{i\})$. Each of these values is either $0$ or $1$. The only possible ordered pairs are therefore $(0,0)$, $(0,1)$, and $(1,1)$, and their differences are respectively $0$, $1$, and $0$. In each case the difference is idempotent under squaring, proving the equality.
