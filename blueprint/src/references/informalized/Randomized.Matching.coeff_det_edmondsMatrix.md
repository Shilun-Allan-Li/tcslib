<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/MatchingMath.lean :: Randomized.Matching.coeff_det_edmondsMatrix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Matching Monomial Coefficient

**Claim.** If a permutation $\tau$ uses only true entries of the Boolean matrix $A$, then the coefficient of its matching monomial in the determinant of the associated polynomial matrix is the sign of $\tau$, viewed in the commutative ring.

**Proof.** Expand the determinant as a sum over permutations, with each summand the permutation sign times the product of the corresponding matrix entries (Randomized.Matching.det_edmondsMatrix_eq_sum). The coefficient of the matching monomial can be taken term by term. For $\tau$, the hypothesis that every selected entry is true makes its product the monomial associated to $\tau$, with coefficient one (Randomized.Matching.prod_edmondsMatrix); multiplying by the sign gives the claimed coefficient. For any other permutation $\sigma$, its product is either zero, if one selected matrix entry vanishes, or its matching monomial. In the latter case that monomial differs from the one for $\tau$, by injectivity of the matching-monomial map (Randomized.Matching.matchMono_injective). Thus every other summand contributes coefficient zero, leaving only the sign of $\tau$.

**Key facts.** `Randomized.Matching.det_edmondsMatrix_eq_sum`, `Randomized.Matching.prod_edmondsMatrix`, `Randomized.Matching.matchMono_injective`.
