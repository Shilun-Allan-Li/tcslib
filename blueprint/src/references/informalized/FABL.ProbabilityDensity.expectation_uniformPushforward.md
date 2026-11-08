<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasGenerator.lean :: FABL.ProbabilityDensity.expectation_uniformPushforward -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation under a uniform pushforward

**Claim.** The expectation of $f$ under the density obtained by pushing forward the uniform distribution on a finite nonempty set $\Omega$ through $g$ equals the uniform expectation of $\omega\mapsto f(g(\omega))$ over $\Omega$.

**Proof.** Write the pushforward density at $x$ as the size of the cube divided by $|\Omega|$, multiplied by the number of points $\omega$ with $g(\omega)=x$. In the expectation of $f$ under this density, the factor equal to the cube size cancels the normalization in the uniform average over the cube. The resulting sum over $x$ weights $f(x)$ by the size of the fiber $g^{-1}(x)$. Equivalently, it sums $f(g(\omega))$ over all points in each fiber and then over all $x$. The fibers partition $\Omega$, so this is the sum of $f(g(\omega))$ over $\omega\in\Omega$, divided by $|\Omega|$, as claimed.
