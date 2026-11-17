<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/NoiseStability.lean :: BooleanAnalysis.ThresholdFunctions.polynomialThresholdClass_closed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closure of Polynomial Thresholds

**Claim.** For fixed $k$, the class of $\{-1,1\}$-valued functions with a polynomial threshold representation of degree at most $k$ is closed under input negation and identification.

**Proof.** Take a function $f$ in the class, represented as the threshold of a degree-at-most-$k$ polynomial $p$, and fix a bit vector $z$ and map $\pi$ identifying the input coordinates. Define a polynomial $q$ on the target cube by assigning to each index set $T$ the sum of $p(S)\chi_S(z)$ over all source sets $S$ whose odd-fiber image under $\pi$ is $T$. If $|T|>k$, every such $S$ has $|S|>k$, because the odd-fiber image has size at most $|S|$; hence all the corresponding coefficients of $p$ vanish. Thus $q$ has degree at most $k$.

For each target input $w$, regrouping the finite sum defining $q(w)$ according to the odd-fiber image gives $q(w)=p(z\text{ with the identified coordinates negated according to }z)$. The key character identity here is that evaluating the source character after negation and identification factors as $\chi_S(z)$ times the target character indexed by the odd-fiber image (\texttt{chiS_identifiedNegation}). Therefore the threshold of $q$ is exactly the transformed function. Finally, every threshold-sign function takes only the values $1$ and $-1$ (\texttt{isPmOne_thresholdSign}), so the transformed function belongs to the class.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.oddFiberImage_card_le`, `BooleanAnalysis.ThresholdFunctions.chiS_identifiedNegation`, `BooleanAnalysis.ThresholdFunctions.isPmOne_thresholdSign`.
