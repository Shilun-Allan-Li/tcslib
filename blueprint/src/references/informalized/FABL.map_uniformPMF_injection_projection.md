<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.map_uniformPMF_injection_projection -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Distribution Under Coordinate Projection

**Claim.** For a finite nonempty set $A$ and an injection $e:\{0,\ldots,M-1\}\hookrightarrow\{0,\ldots,R-1\}$, restricting a uniformly chosen function $x:\{0,\ldots,R-1\}\to A$ along $e$ gives the uniform distribution on functions from $\{0,\ldots,M-1\}$ to $A$.

**Proof.** Split each function on the larger index set into its restriction along $e$ and its values on the complement of the image of $e$. This gives a bijection between functions on the larger set and pairs consisting of a function on the smaller set and a function on that complement. Mapping the uniform distribution through this bijection gives the uniform distribution on the product space by the uniform-distribution-under-bijection result (\texttt{map\_uniformPMF\_equiv}). Projection onto the first factor then gives the uniform distribution on functions on the smaller index set (\texttt{map\_uniformPMF\_fst}). Since the first component of the split is precisely restriction along $e$, this is the desired distribution.

**Key facts.** `FABL.map_uniformPMF_equiv`, `FABL.map_uniformPMF_fst`.
