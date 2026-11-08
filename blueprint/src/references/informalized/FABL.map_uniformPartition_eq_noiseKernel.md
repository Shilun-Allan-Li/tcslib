<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/UniformNoiseStability.lean :: FABL.map_uniformPartition_eq_noiseKernel -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Partition Flips Give a Noise Kernel

**Claim.** For $m>0$, a uniformly chosen map from the $n$ coordinates to $m$ labels, used to negate $x_i$ precisely when coordinate $i$ receives the chosen label, produces the noise-kernel distribution with correlation $1-2/m$.

**Proof.** The uniformly chosen map assigns labels independently and uniformly across coordinates. Consequently, the output sign vector has the independent-coordinate distribution whose $i$th coordinate is obtained by flipping $x_i$ when its label is the chosen one (`map_uniformFunctionPMF_eq_independentProductPMF`). For a single coordinate, exactly one of the $m$ equally likely labels triggers a flip, so the keep probability is $1-1/m$. The coordinate flip law is therefore the coordinate noise law with correlation $1-2/m$ (`map_uniformFin_fiberFlip_eq_coordinateNoisePMF`). The parameter is admissible because $1/m$ lies in $[0,1]$ (`inverseDimension_mem_Icc`), and hence $1-2/m$ lies in $[-1,1]$ (`one_sub_two_mul_mem_Icc`). Combining the coordinate laws gives the asserted noise kernel.

**Key facts.** `FABL.map_uniformFunctionPMF_eq_independentProductPMF`, `FABL.inverseDimension_mem_Icc`, `FABL.one_sub_two_mul_mem_Icc`, `FABL.map_uniformFin_fiberFlip_eq_coordinateNoisePMF`.
