<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.mul_half_pow_lmnLayerCutoff_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Layer Cutoff Exponential Bound

**Claim.** For positive $s$ and $\varepsilon$, the layer cutoff $L$ satisfies $s(1/2)^L\le\varepsilon/2$.

**Proof.** Apply the reciprocal cutoff bound `mul_inv_two_pow_dnfWidthTruncationCutoff_le` with error parameter $\varepsilon/2$, which is positive. By definition, the layer cutoff is the width cutoff for that parameter, so the result gives $s\,2^{-L}\le\varepsilon/2$. Since $2^{-L}=(1/2)^L$, this is the claimed inequality.

**Key facts.** `FABL.mul_inv_two_pow_dnfWidthTruncationCutoff_le`.
