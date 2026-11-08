<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/AC0ThresholdParitySeparation.lean :: FABL.blockCoordinateValue_lt_active -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Block coordinate value bound

**Claim.** For every $m$, $b<m$, and $j<2m$, the block coordinate value is strictly less than $2m^2$.

**Proof.** Split according to whether $j<m$. In the first case the value is $bm+j$. Since $j<m$ and $b+1\le m$, we have $bm+j<(b+1)m\le m^2$, hence it is less than $2m^2$. In the second case, $m\le j<2m$, so $j-m<m$; the value is $m^2+bm+(j-m)$. The same estimate gives $bm+(j-m)<(b+1)m\le m^2$, so this value too is less than $2m^2$.
