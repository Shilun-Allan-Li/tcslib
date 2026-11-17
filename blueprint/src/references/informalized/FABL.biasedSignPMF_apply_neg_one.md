<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.biasedSignPMF_apply_neg_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mass at the Negative Sign

**Claim.** For $p\in[0,1]$, the biased sign distribution assigns mass $1-\kappa$ to $-1$, where $\kappa$ is the keep probability associated to the mean bias $1-2p$.

**Proof.** The distribution is obtained by choosing whether to keep the initial sign $1$ or flip it. The outcome $-1$ occurs exactly when the sign is flipped, so its mass is the complementary probability $1-\kappa$, with $\kappa$ the keep probability at bias mean $1-2p$.

**Key facts.** `FABL.biasMean_mem_Icc`.
