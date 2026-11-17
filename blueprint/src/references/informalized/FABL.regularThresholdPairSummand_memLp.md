<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RegularThresholdNoiseStability.lean :: FABL.regularThresholdPairSummand_memLp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Third-Moment Integrability of a Pair Summand

**Claim.** Each coordinate pair summand belongs to $L^3$ under the correlated-pair distribution.

**Proof.** The space of pairs of sign vectors of length $n$ is finite. Consequently, the norm of the summand, as a function on that space, has a finite upper bound $C$. The summand is measurable on this finite space, and its norm is everywhere at most $C$. A measurable function with a uniform norm bound belongs to $L^p$ for every finite exponent under a probability measure; applying this boundedness criterion with $p=3$ proves the claim.
