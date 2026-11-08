<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/SizeClasses.lean :: BoolCircuit.prod_fin_two_eq_one_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# When a Product of Bits Is One

**Claim.** For a finite index type and elements $x_i\in\mathrm{Fin}(2)$, the product $\prod_i x_i$ equals $1$ if and only if every $x_i$ equals $1$.

**Proof.** If the product is $1$, fix any index $i$ and separate its factor from the product of all the other factors. In $\mathrm{Fin}(2)$, a product equal to $1$ forces each factor to be $1$; applying this to the separated factor shows $x_i=1$. Since $i$ was arbitrary, every factor is $1$. Conversely, if every factor is $1$, the product is a product of identities and therefore equals $1$.
