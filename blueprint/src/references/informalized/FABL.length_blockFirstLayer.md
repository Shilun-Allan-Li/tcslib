<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/AC0ThresholdParitySeparation.lean :: FABL.length_blockFirstLayer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the first block layer

**Claim.** For every natural number $m$ with $7\le m$, the first block layer contains exactly $m\,2^{2m}$ terms.

**Proof.** The first block layer is formed with one list entry for each element of a finite index set of size $\mathrm{blockLayerSize}(m)$. A list built from a function on a finite index set has length equal to the size of that index set, so the layer length is $m\,2^{m+m}$. Since $m+m=2m$, this is $m\,2^{2m}$.
