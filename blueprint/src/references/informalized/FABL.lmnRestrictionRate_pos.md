<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.lmnRestrictionRate_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of the restriction rate

**Claim.** Under the stated bounds on $s$ and $\varepsilon$, the circuit compression rate with width cutoff $W$, layer cutoff $L$, and exponent $d-2$ is positive.

**Proof.** The width cutoff is positive by `lmnWidthCutoff_pos`. Since $s>1$, it is also a positive integer, and $\varepsilon/12$ is positive and at most $1$. Thus `lmnLayerCutoff_pos` shows that the layer cutoff evaluated at $\varepsilon/12$ is positive. The switching-layer rate is $1/(10w)$, so it is positive at each of these positive cutoffs. Finally, the circuit compression rate is the width rate multiplied by the layer rate raised to the natural exponent $d-2$; a positive number raised to any natural power remains positive, and so does this product.

**Key facts.** `FABL.lmnWidthCutoff_pos`, `FABL.lmnLayerCutoff_pos`.
