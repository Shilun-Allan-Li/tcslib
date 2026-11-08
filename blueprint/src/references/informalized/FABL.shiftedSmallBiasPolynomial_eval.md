<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasVariants.lean :: FABL.shiftedSmallBiasPolynomial_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the shifted polynomial

**Claim.** The shifted polynomial with binary coefficients, evaluated at $r$, equals the field pairing of those coefficients with the sequence of powers $1,r,r^2,\ldots,r^{n-1}$.

**Proof.** Evaluate the defining finite sum term by term. Polynomial evaluation sends each coefficient polynomial to its coefficient and sends $X^i$ to $r^i$, so the result is the sum over $i$ of the image of $\gamma_i$ multiplied by $r^i$. Scalar multiplication by a binary-field element in the field is multiplication by its image under the algebra map. The sequence paired with $\gamma$ is precisely $i\mapsto r^i$, giving the stated field pairing.
