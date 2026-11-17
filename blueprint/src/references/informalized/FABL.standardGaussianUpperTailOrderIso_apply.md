<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetric.lean :: FABL.standardGaussianUpperTailOrderIso_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Tail Order-Isomorphism Formula

**Claim.** For every real number $t$, the standard Gaussian upper-tail order isomorphism, applied to $t$ with the order reversed on the real line, equals the standard Gaussian upper-tail probability at $t$.

**Proof.** By definition, the order isomorphism is built from the function that sends each reversed-order real number to the corresponding open-interval point whose real value is the standard Gaussian upper tail. Applying the isomorphism therefore returns that interval point; taking its real value gives exactly the standard Gaussian upper tail at $t$.
