<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasGenerator.lean :: FABL.smallBiasPolynomial_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the small-bias polynomial

**Claim.** Evaluating the polynomial whose coefficient of $X^{i+1}$ is the image of the $i$th coordinate of $\gamma$ gives $\sum_{i=0}^{n-1}\gamma_i r^{i+1}$.

**Proof.** Expand the polynomial as its defining finite sum. Evaluation distributes over finite sums, and evaluating the term $C(\gamma_i)X^{i+1}$ at $r$ gives $C(\gamma_i)r^{i+1}$. In the extension field, multiplication by the scalar image of $\gamma_i$ is precisely scalar multiplication, so each term is $\gamma_i\,\bullet\,r^{i+1}$. Summing these identities gives the stated formula.
