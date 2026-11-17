<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/General.lean :: BooleanAnalysis.Hypercontractivity.product_lowDegree_projection -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low-degree projection bound

**Claim.** For every real $q>1$, there is a constant $C\ge 1$ such that the degree-at-most-$k$ projection on any finite product probability space satisfies $\|f^{\le k}\|_{q,P}\le C^k\|f\|_{q,P}$. When $q=4$ or $q=4/3$, one can take $C=5\sqrt{3}$.

**Proof.** Split according to whether $q\ge2$. In that range, apply the projection bound above the second moment to obtain a suitable $C$ and the norm estimate; its special value at $q=4$ gives the required constant there. The case $q=4/3$ cannot occur in this range. If instead $1<q<2$, set $p=q/(q-1)$. Then $p\ge2$, so the bound above the second moment applies to the exponent $p$. The conjugate exponent of $p$ is $q$. The projection is self-adjoint with respect to expectation, and the self-adjoint norm-transfer bound therefore converts its $p$-norm estimate into the desired $q$-norm estimate, with the same constant. If $q=4/3$, then $p=4$, so the constant is $5\sqrt{3}$; the case $q=4$ is excluded from this second range.

**Key facts.** `BooleanAnalysis.Hypercontractivity.product_lowDegree_projection_ge_two`, `BooleanAnalysis.Hypercontractivity.RandomizationProjectionAux.product_lowDegree_selfAdjoint`, `BooleanAnalysis.Hypercontractivity.RandomizationProjectionAux.product_selfAdjoint_bound`.
