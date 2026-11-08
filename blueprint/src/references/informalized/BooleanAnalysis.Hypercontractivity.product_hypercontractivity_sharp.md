<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/General.lean :: BooleanAnalysis.Hypercontractivity.product_hypercontractivity_sharp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sharp Product Hypercontractivity

**Claim.** Under the stated assumptions, if $0\le\rho\le r$, then the product noise operator satisfies both $\|T_\rho f\|_{q,P}\le\|f\|_{2,P}$ and $\|T_\rho f\|_{2,P}\le\|f\|_{q/(q-1),P}$.

**Proof.** Because $q>2$, we have $q>1$, and $q$ and $q/(q-1)$ are Hölder conjugates. Also, the sharp radius $r$ is less than $1$ under $0<\lambda<1/2$ and $q>2$, so $\rho\le1$.

The sharp one-coordinate theorem gives both required coordinate norm inequalities: one from exponent $2$ to $q$, and the other from exponent $q/(q-1)$ to $2$. Apply product tensorization above the first moment to the first coordinate inequality with $(p,q)=(2,q)$, and then to the second with $(p,q)=(q/(q-1),2)$. The conjugate-exponent relation ensures the latter input exponent is at least $1$. These two applications give the asserted pair of product bounds.

**Key facts.** `BooleanAnalysis.Hypercontractivity.SharpDiscrete.radius_pos_lt_one`, `BooleanAnalysis.Hypercontractivity.finite_coordinate_hypercontractivity_sharp`, `BooleanAnalysis.Hypercontractivity.product_hypercontractivity_induction_gt_one`.
