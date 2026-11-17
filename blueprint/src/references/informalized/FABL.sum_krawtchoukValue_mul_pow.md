<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/KrawtchoukPolynomials.lean :: FABL.sum_krawtchoukValue_mul_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Krawtchouk Generating Sum

**Claim.** The degree-weighted sum of Krawtchouk values equals the sum over all subsets, where each subset contributes its monomial times $\rho$ raised to its size.

**Proof.** Expand each degree-$j$ Krawtchouk value as a sum over subsets of size $j$ and distribute the factor $\rho^j$ into that sum. Every subset of the coordinate set has size at most $n$, so it appears in exactly the term indexed by its size. Regrouping the finite sum by subsets therefore gives the asserted identity.
