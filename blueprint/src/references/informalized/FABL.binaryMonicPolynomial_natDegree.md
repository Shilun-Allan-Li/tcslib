<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryMonicPolynomial_natDegree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Natural Degree of the Binary Polynomial

**Claim.** For every natural number $\ell$ and coefficient vector $a\in\mathbb{F}_2^\ell$, the associated monic polynomial has natural degree $\ell$.

**Proof.** The polynomial's degree is $\ell$ (`binaryMonicPolynomial_degree`). In particular, its degree is finite, and its natural degree is the natural number represented by that degree. Hence its natural degree is $\ell$.

**Key facts.** `FABL.binaryMonicPolynomial_degree`.
