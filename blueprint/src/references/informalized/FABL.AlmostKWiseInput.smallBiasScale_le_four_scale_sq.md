<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/AlmostKWiseAlgorithm.lean :: FABL.AlmostKWiseInput.smallBiasScale_le_four_scale_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Small bias scale bound

**Claim.** The scale computed from the row count is at most four times the square of one plus the scale computed from the output dimension.

**Proof.** Let $s$ be the output-dimension scale and $d$ the field degree. By the defining property of ceiling division, $nD\le Ns$. The row-count bound by the size scale, together with $k\le n$, gives $r\le n(d+1)$. Multiplying by $D$ and using $nD\le Ns$ shows $rD\le N(d+1)s$; applying the ceiling-division characterization again yields that the small-bias scale is at most $(d+1)s$. The field-degree bound and $n\le s$ give $d+1\le4(n+1)\le4(s+1)$. Also $s\le s+1$, so $(d+1)s\le4(s+1)^2$. Combining these estimates proves the claim.

**Key facts.** `FABL.AlmostKWiseInput.rowCount_le_sizeScale`, `FABL.AlmostKWiseInput.n_le_scale`, `FABL.ExecutableVandermondeInput.fieldDegree_succ_le`.
