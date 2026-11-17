<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean :: CommunicationComplexity.exp_sub_cgf_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Factorisation of the tilted exponential

**Claim.** For every $x\in\Omega$, the exponential of $tX(x)-\Lambda(t)$ equals $e^{-\Lambda(t)}e^{tX(x)}$, where $\Lambda(t)$ is the cumulant generating function at $t$.

**Proof.** Fix $x$. Split the exponent as $tX(x)+(-\Lambda(t))$. The exponential of a sum is the product of the exponentials, giving $e^{tX(x)}e^{-\Lambda(t)}$. Since multiplication in $\mathbb R$ is commutative, this is the stated factorisation.
