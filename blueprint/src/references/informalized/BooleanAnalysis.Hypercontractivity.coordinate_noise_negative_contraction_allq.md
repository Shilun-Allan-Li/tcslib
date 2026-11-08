<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/Contraction.lean :: BooleanAnalysis.Hypercontractivity.coordinate_noise_negative_contraction_allq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negative noise contraction above one

**Claim.** For every $q>1$, there is a parameter $0<c\le1$, equal to $2/5$ when $q=4$ or $q=4/3$, for which negative coordinate noise contracts the $q$-norm on every finite product space.

**Proof.** Split into the cases $q\ge2$ and $1<q<2$. In the first case, apply the negative-contraction theorem for exponents at least two; the exceptional value $q=4/3$ cannot occur there. In the second case, put $p=q/(q-1)$. The inequalities $q>1$ and $q<2$ imply $p\ge2$, so the same theorem supplies $c$ and contraction at exponent $p$. At $q=4$, the second case is impossible; at $q=4/3$, one has $p=4$, so the chosen parameter is $2/5$. To transfer contraction back from $p$ to $q$, use self-adjointness of the coordinate-noise operator and the finite weighted-space duality principle: a self-adjoint operator contracting the $p$-norm contracts the conjugate $q$-norm. The product mass weights are nonnegative, as required by that principle.

**Key facts.** `BooleanAnalysis.Hypercontractivity.coordinate_noise_negative_contraction`, `BooleanAnalysis.Hypercontractivity.FiniteNorms.selfAdjoint_contraction`, `BooleanAnalysis.Hypercontractivity.coordinateNoise_selfAdjoint`.
