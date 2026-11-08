<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryMonicPolynomial_monic -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monicity of the Binary Polynomial

**Claim.** For every natural number $\ell$ and coefficient vector $a\in\mathbb{F}_2^\ell$, the polynomial $X^\ell+\sum_{i=0}^{\ell-1}a_iX^i$ is monic over $\mathbb{F}_2$.

**Proof.** The low polynomial has degree strictly less than $\ell$ (`binaryLowPolynomial_degree_lt`). Adding a polynomial of lower degree to the monic polynomial $X^\ell$ preserves its leading coefficient, so the resulting polynomial is monic.

**Key facts.** `FABL.binaryLowPolynomial_degree_lt`.
