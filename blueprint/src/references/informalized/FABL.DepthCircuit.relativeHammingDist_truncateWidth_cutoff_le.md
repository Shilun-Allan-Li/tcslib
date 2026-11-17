<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.DepthCircuit.relativeHammingDist_truncateWidth_cutoff_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Truncation Error at the Cutoff

**Claim.** For a positive error tolerance $\varepsilon$, truncating the circuit at the prescribed width cutoff changes its Boolean function on at most an $\varepsilon$ fraction of inputs.

**Proof.** Apply the truncation error bound: for any width $w$, the relative Hamming distance between the original circuit and its width-$w$ truncation is at most $C.size\,2^{-w}$ (that is, $C.size$ times the reciprocal of $2^w$) (`FABL.DepthCircuit.relativeHammingDist_truncateWidth_le`). Set $w$ to the prescribed cutoff. If $C.size=0$, the resulting bound is zero, hence at most $\varepsilon$. If $C.size>0$, the cutoff estimate gives $C.size\,2^{-w}\leq\varepsilon$ (`FABL.mul_inv_two_pow_dnfWidthTruncationCutoff_le`). Combining these inequalities proves the claim.

**Key facts.** `FABL.DepthCircuit.relativeHammingDist_truncateWidth_le`, `FABL.mul_inv_two_pow_dnfWidthTruncationCutoff_le`.
