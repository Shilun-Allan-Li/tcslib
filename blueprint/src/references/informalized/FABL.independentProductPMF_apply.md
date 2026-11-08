<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseKernels.lean :: FABL.independentProductPMF_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Point probabilities of an independent product

**Claim.** For a finite index set, the independent product distribution assigns a tuple the product of its coordinate probabilities.

**Proof.** By definition, the independent product is built from the point-mass function that sends each tuple $x$ to $\prod_{i\in I} p_i(x_i)$. Evaluating the resulting probability mass function at $x$ therefore gives exactly this product.
