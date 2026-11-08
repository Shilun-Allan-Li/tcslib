<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/General.lean :: BooleanAnalysis.Hypercontractivity.product_hypercontractivity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite Product Hypercontractivity

**Claim.** Under the stated atom lower bound and parameter assumptions, the product noise operator satisfies both $\|T_\rho f\|_{q,P}\le\|f\|_{2,P}$ and $\|T_\rho f\|_{2,P}\le\|f\|_{q/(q-1),P}$.

**Proof.** Split according to whether $\lambda<1$ or $\lambda=1$. If $\lambda<1$, set $\lambda'=\lambda/(1+\lambda)$. Then $0<\lambda'<1/2$, and each coordinate weight is at least $\lambda'$, since $\lambda/(1+\lambda)\le\lambda$. The sharp product hypercontractivity theorem applies at this smaller parameter. Its allowable noise radius is at least the radius in the hypothesis: this is the comparison supplied by `coarse_radius_le_sharp`. Hence the assumed bound on $\rho$ implies both desired inequalities.

If $\lambda=1$, apply the unit-atom case `product_hypercontractivity_atom_one`, which gives both inequalities directly.

**Key facts.** `BooleanAnalysis.Hypercontractivity.coarse_radius_le_sharp`, `BooleanAnalysis.Hypercontractivity.product_hypercontractivity_sharp`, `BooleanAnalysis.Hypercontractivity.product_hypercontractivity_atom_one`.
