<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FiniteProbabilitySpace.lean :: CommunicationComplexity.FiniteProbabilitySpace.pmf_prod -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product probability masses

**Claim.** For finite probability spaces $\Omega_1$ and $\Omega_2$, the probability mass of $(x,y)$ in the product space is the product of the individual masses at $x$ and $y$.

**Proof.** Fix $x\in\Omega_1$ and $y\in\Omega_2$. By the definition of the mass function associated to a measure, its value at a point is the measure of that singleton. The singleton $\{(x,y)\}$ is the rectangle $\{x\}\times\{y\}$. The product space's volume measure is the product of the two volume measures, and the product-measure formula on rectangles gives $\operatorname{volume}(\{x\}\times\{y\})=\operatorname{volume}(\{x\})\operatorname{volume}(\{y\})$. These are exactly the two individual masses, proving the equality.
