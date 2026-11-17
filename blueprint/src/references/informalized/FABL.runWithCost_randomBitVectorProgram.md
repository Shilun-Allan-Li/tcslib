<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DerandomizedBLRProgram.lean :: FABL.runWithCost_randomBitVectorProgram -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Random Bit Vectors

**Claim.** Generating $b$ independent unbiased bits yields a uniform vector in $	ext{Fin}(b)\to\text{Bool}$, paired with the fixed cost $(0,0,b)$.

**Proof.** Induct on $b$. For $b=0$, there is only one function from the empty index set to the Boolean values, so the uniform law is a point mass; the program returns it with zero cost. For the successor step, the program draws a uniform Boolean head and independently generates the tail vector. By induction the tail is uniform, and the accumulated cost is $(0,0,b+1)$ because one coin draw adds $(0,0,1)$. Independent uniform choices on the head and tail give the uniform law on their product (the fact supplied by `uniformPMF_bind_map_pair`). The equivalence between a Boolean vector indexed by $	ext{Fin}(b+1)$ and a head together with a $	ext{Fin}(b)$ tail then identifies this product law with the uniform vector law (`map_uniformPMF_equiv`). The zero-length case uses the unique empty vector law (`uniformPMF_finZeroArrowBool`).

**Key facts.** `FABL.uniformPMF_finZeroArrowBool`, `FABL.LearningProgram.runWithCost_map`, `FABL.LearningCost.toTriple_injective`, `FABL.uniformPMF_bind_map_pair`, `FABL.map_uniformPMF_equiv`.
