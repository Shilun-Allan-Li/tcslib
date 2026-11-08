<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/ProjectionBounds.lean :: BooleanAnalysis.Hypercontractivity.RandomizationProjectionAux.product_selfAdjoint_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Self-adjoint norm bound

**Claim.** Under the stated self-adjointness and conjugate-exponent norm bound, the operator satisfies the corresponding norm bound at exponent $q$: for every $f$, $\|Tf\|_{q,P}\le A\|f\|_{q,P}$.

**Proof.** Fix $f$ and rescale the operator by setting $Ug=A^{-1}Tg$. Since $A>0$, this preserves self-adjointness, and the assumed bound at exponent $q/(q-1)$ gives $\|Ug\|_{q/(q-1),P}\le\|g\|_{q/(q-1),P}$ for every $g$. The self-adjoint contraction principle says that an operator self-adjoint with respect to a nonnegative weighted inner product and contractive at the conjugate exponent is also contractive at exponent $q$ (`selfAdjoint_contraction`). Apply it with the product masses as weights; they are nonnegative because each coordinate weight is positive. Thus $\|Uf\|_{q,P}\le\|f\|_{q,P}$. Finally, homogeneity of the product norm for a nonnegative scalar gives $\|A^{-1}Tf\|_{q,P}=A^{-1}\|Tf\|_{q,P}$. Multiplying the contraction inequality by $A>0$ yields the claim.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteNorms.selfAdjoint_contraction`, `BooleanAnalysis.Hypercontractivity.RandomizationProjectionAux.product_norm_const_mul`.
