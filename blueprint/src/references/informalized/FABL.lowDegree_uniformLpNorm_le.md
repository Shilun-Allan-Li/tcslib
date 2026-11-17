<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ProductHypercontractivity.lean :: FABL.lowDegree_uniformLpNorm_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low-degree norm bound

**Claim.** For $q\ge2$ and a function of Fourier degree at most $k$, its uniform $L^q$ norm is at most $(q-1)^{k/2}$ times its uniform $L^2$ norm.

**Proof.** If $q=2$, the assertion is equality. For $q>2$, let $r=\sqrt{q-1}$ and apply the noise operator with parameter $r$ to $f$. Applying the noise operator again with parameter $1/r$ recovers $f$, because noise parameters multiply under composition and the operator with parameter $1$ is the identity (`noiseOperator_comp`, `noiseOperator_one`). The $(2,q)$ hypercontractive inequality applied to the smoothed function bounds the $L^q$ norm of this recovered function by the $L^2$ norm of the smoothed function (`twoQHypercontractivity_of_two_lt`). Since $r\ge1$, the degree bound gives that latter norm at most $r^k\|f\|_2$ (`uniformLpNorm_two_noiseOperator_le_pow_of_degree`). Finally $r^k=(q-1)^{k/2}$, as required.

**Key facts.** `FABL.noiseOperator_comp`, `FABL.noiseOperator_one`, `FABL.twoQHypercontractivity_of_two_lt`, `FABL.uniformLpNorm_two_noiseOperator_le_pow_of_degree`.
