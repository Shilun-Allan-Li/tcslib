<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/FiniteFields.lean :: FABL.binaryExtensionField_finrank -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dimension of the Binary Extension

**Claim.** For every positive integer $\ell$, the degree-$\ell$ extension field of $\mathbb{F}_2$ has dimension $\ell$ as a vector space over $\mathbb{F}_2$.

**Proof.** The dimension formula for a finite Galois field states that the field $\mathrm{GaloisField}(p,\ell)$ has vector-space dimension $\ell$ over its prime field when $\ell>0$. Apply this with $p=2$; the hypothesis $\ell\ne0$ gives the required positivity, so the dimension is $\ell$.
