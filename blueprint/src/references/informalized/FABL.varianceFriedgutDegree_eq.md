<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/VarianceSensitiveLargeCoefficient.lean :: FABL.varianceFriedgutDegree_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance based Friedgut degree formula

**Claim.** If a Boolean function $f$ has positive variance, then its variance based Friedgut degree is the ceiling of $8$ times its total influence divided by its variance.

**Proof.** By definition, the variance based degree is the Friedgut degree at error equal to one eighth of the variance. Substituting this error into the degree formula gives the ceiling of total influence divided by $\operatorname{Var}(f)/8$. Since the variance is positive, division by it is valid, and this quotient simplifies to $8\operatorname{Inf}(f)/\operatorname{Var}(f)$. Taking the natural-number ceiling gives the claimed identity.
