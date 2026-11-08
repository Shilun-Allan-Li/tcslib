<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.integral_bernoulliSubsetMass_eq_shapleyLayerWeight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bernoulli Subset Mass and Shapley Weight

**Claim.** For $k\le n$, the integral of $p^k(1-p)^{n-k}$ from $0$ to $1$ equals $1/((n+1)\binom{n}{k})$.

**Proof.** The integral of powers on the unit interval (\(\texttt{integral\_pow\_mul\_one\_sub\_pow}\)) gives $k!(n-k)!/(n+1)!$. The binomial coefficient identity $\binom{n}{k}k!(n-k)!=n!$, together with $(n+1)!=(n+1)n!$, rewrites this quotient as $1/((n+1)\binom{n}{k})$. The hypothesis $k\le n$ ensures the binomial coefficient is positive, so the rearrangement is valid.

**Key facts.** `FABL.integral_pow_mul_one_sub_pow`.
