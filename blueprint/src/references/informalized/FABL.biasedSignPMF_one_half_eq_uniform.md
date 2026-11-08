<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.biasedSignPMF_one_half_eq_uniform -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniformity at Half Bias

**Claim.** At $p=\tfrac12$, the biased sign distribution on $\{\pm1\}$ is the uniform probability distribution.

**Proof.** Two probability distributions on the finite sign space are equal once their masses agree at each sign. Compare their real-valued masses: by the biased-mass formula, each sign has mass $1/2$ when $p=1/2$. The uniform distribution on a two-element space also assigns mass $1/2$ to each sign. Thus the distributions agree at both possible signs, and so are equal.

**Key facts.** `FABL.biasedSignPMF_apply_toReal`.
