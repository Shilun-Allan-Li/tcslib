<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/MatchingMath.lean :: Randomized.Matching.matchMono_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Entries of a Matching Monomial

**Claim.** At the variable indexed by $(a,b)$, the matching monomial for $\sigma$ has exponent $1$ if $\sigma(a)=b$, and exponent $0$ otherwise.

**Proof.** Evaluate the defining finite sum of single-coordinate exponent vectors at $(a,b)$. Every summand is zero there except possibly the one indexed by $a$, since a single-coordinate vector is supported only at its designated pair. The remaining summand contributes $1$ exactly when its designated pair $(a,\sigma(a))$ equals $(a,b)$, which is equivalent to $\sigma(a)=b$. Thus the exponent is the stated indicator.
