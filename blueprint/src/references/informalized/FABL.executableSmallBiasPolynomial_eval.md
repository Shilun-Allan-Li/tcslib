<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasAlgorithm.lean :: FABL.executableSmallBiasPolynomial_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the Generator Polynomial

**Claim.** For a certified binary field implementation, a binary vector $\gamma$ of length $n$, and any extension-field element $r$, evaluating the associated generator polynomial at $r$ gives $\sum_{i=0}^{n-1}\gamma_i r^{i+1}$, with each coefficient acting by scalar multiplication.

**Proof.** Evaluate the defining finite sum term by term. Evaluation sends each coefficient polynomial to the image of $\gamma_i$ in the extension field and sends $X^{i+1}$ to $r^{i+1}$. The product of these is the scalar action of that coefficient on the power, by the definition of scalar multiplication induced by the field algebra structure. Summing over $i\in\mathrm{Fin}(n)$ gives the stated expression.
