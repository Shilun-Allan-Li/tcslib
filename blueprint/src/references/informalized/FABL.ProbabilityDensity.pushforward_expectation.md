<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/ProbabilityDensityPushforward.lean :: FABL.ProbabilityDensity.pushforward_expectation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation under a pushforward density

**Claim.** The expectation of $g$ under the pushforward of $\varphi$ by $L$ equals the expectation under $\varphi$ of $y\mapsto g(L(y))$.

**Proof.** Expand the pushforward expectation using its defining density. Rearranging the factors inside each summand places $g(z)$ next to the uniform mean over $y$ of $\varphi(y)$ when $L(y)=z$, and zero otherwise. The target-cube size cancels the normalization of the uniform average over the target cube, leaving a sum over $z$ of these input averages multiplied by $g(z)$. Exchange the finite sum over $z$ with the uniform expectation over $y$. For each fixed $y$, exactly one target point contributes, namely $z=L(y)$, so the inner sum reduces to $\varphi(y)g(L(y))$. This is the expectation of $g\circ L$ under $\varphi$, by definition.
