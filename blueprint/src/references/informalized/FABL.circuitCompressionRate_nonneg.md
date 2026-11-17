<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.circuitCompressionRate_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative Compression Rate

**Claim.** For all natural numbers $w,\ell,r$, the circuit compression rate $R(w,\ell,r)=a_w a_\ell^r$ is nonnegative, where each switching-layer rate $a_j$ is nonnegative.

**Proof.** The rate is the product of the switching-layer rate at $w$ and the $r$th power of the switching-layer rate at $\ell$. Each switching-layer rate is nonnegative (`FABL.switchingLayerRate_nonneg`), so its natural-number power is nonnegative as well. The product of these two nonnegative quantities is nonnegative.

**Key facts.** `FABL.switchingLayerRate_nonneg`.
