<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/General.lean :: BooleanAnalysis.Hypercontractivity.one_coordinate_hypercontractivity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-coordinate hypercontractivity

**Claim.** Under the stated atom-weight and parameter assumptions, on a product consisting of one finite probability space, both $\|T_\rho f\|_q\le\|f\|_2$ and $\|T_\rho f\|_2\le\|f\|_{q/(q-1)}$ hold.

**Proof.** Apply the product hypercontractivity theorem to the one-coordinate product space with the given atom lower bound $\lambda$ and parameters $q,\rho$. Its hypotheses are precisely the assumed positivity and upper bound for $\lambda$, the atom-weight condition, $q>2$, $\rho\ge0$, and the stated bound on $\rho$. The theorem yields both norm inequalities at once (`product_hypercontractivity`).

**Key facts.** `BooleanAnalysis.Hypercontractivity.product_hypercontractivity`.
