<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryMonicPolynomial_degree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree of the Binary Monic Polynomial

**Claim.** For every natural number $\ell$ and coefficient vector $a\in\mathbb{F}_2^\ell$, the polynomial $X^\ell+\sum_{i=0}^{\ell-1}a_iX^i$ has degree $\ell$.

**Proof.** The low polynomial has degree strictly less than $\ell$ (`binaryLowPolynomial_degree_lt`). Therefore, when it is added to $X^\ell$, the degree of the sum remains the degree of the higher-degree summand. Since $X^\ell$ has degree $\ell$, the associated monic polynomial has degree $\ell$.

**Key facts.** `FABL.binaryLowPolynomial_degree_lt`.
