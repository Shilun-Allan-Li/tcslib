<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/AC0ThresholdParitySeparation.lean :: FABL.blockCoordinate_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of block coordinates

**Claim.** For $m\ge7$ and fixed $b<m$, distinct indices $i,j<2m$ have distinct block coordinates.

**Proof.** Suppose the block coordinates of $i$ and $j$ agree, and compare their natural-number values. If both indices are below $m$, their values are $bm+i$ and $bm+j$, so equality gives $i=j$. If exactly one index is below $m$, its value is less than $m^2$, whereas the other value is at least $m^2$; equality is impossible. If both are at least $m$, their values are $m^2+bm+(i-m)$ and $m^2+bm+(j-m)$, and equality again gives $i=j$. Equality of the coordinates in the finite type implies equality of their values, so these cases prove injectivity. The hypothesis $m\ge7$ is used in constructing the coordinates within the ambient dimension, not in distinguishing their values.
