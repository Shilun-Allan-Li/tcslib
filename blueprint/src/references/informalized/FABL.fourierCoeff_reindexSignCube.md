<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/AC0ThresholdParitySeparation.lean :: FABL.fourierCoeff_reindexSignCube -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficients under reindexing

**Claim.** If $e:[k]\to\iota$ is a bijection, then reindexing the inputs of a function on sign assignments to $\iota$ makes its Fourier coefficient at $S\subseteq[k]$ equal the coefficient of the original function at the image $e(S)$.

**Proof.** The reindexing map is a bijection between the two sign cubes, so changing variables in the uniform expectation gives the coefficient as an expectation over sign assignments to $\iota$. Under this change of variables, the character on $S$ becomes the character on its image $e(S)$: the product over $S$ reindexes to the product over the mapped set. The resulting expectation is precisely the Fourier coefficient at $e(S).$
