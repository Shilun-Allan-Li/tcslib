<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Replacement.lean :: BooleanAnalysis.GaussianSpace.independent_affine_comparison_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Independent affine comparison bound

**Claim.** If $U$ and $V$ are each independent of $(A,D)$ and the pointwise scalar comparison is bounded by $B$, then the difference between the expectations of $\psi(A+DU)$ and $\psi(A+DV)$ is bounded in absolute value by the expectation of $B(A,D)$.

**Proof.** Independence gives an integral formula for each expectation: integrate first over the independent variable while holding $(A,D)=(a,d)$ fixed, then integrate the resulting function against the law of $(A,D)$ (`independent_affine_integral`). Subtract these two formulas and combine the integrals, which is valid by the assumed integrability. The absolute value of an integral is at most the integral of the absolute value. At each pair $(a,d)$, the assumed scalar comparison bounds that absolute value by $B(a,d)$; integrating this pointwise bound against the law of $(A,D)$ gives the desired inequality. The resulting integral of $B$ against that law equals the expectation of $B(A,D)$ by the change-of-variables formula for the distribution of a measurable random vector.

**Key facts.** `BooleanAnalysis.GaussianSpace.independent_affine_integral`.
