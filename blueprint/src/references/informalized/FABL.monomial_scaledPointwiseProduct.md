<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadTests.lean :: FABL.monomial_scaledPointwiseProduct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monomial of a Scaled Pointwise Product

**Claim.** The monomial of the pointwise product scaled by $b$ equals $\operatorname{signValue}(b)^{|S|}$ times the monomials of $x$ and $y$.

**Proof.** Expand the monomial over $S$ and use multiplicativity of sign value to write each factor from $b x_i y_i$ as $\operatorname{signValue}(b)\operatorname{signValue}(x_i)\operatorname{signValue}(y_i)$. Separating the finite product gives one copy of $\operatorname{signValue}(b)$ for every index in $S$, hence the power $|S|$, together with the two monomials.
