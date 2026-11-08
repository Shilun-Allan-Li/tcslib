<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.biasMean_mem_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Range of the Bias Mean

**Claim.** For every $p\in[0,1]$, the bias mean $1-2p$ belongs to $[-1,1]$.

**Proof.** The lower bound $p\ge 0$ implies $1-2p\le 1$. The upper bound $p\le 1$ implies $1-2p\ge -1$. Together these give the stated interval membership.
