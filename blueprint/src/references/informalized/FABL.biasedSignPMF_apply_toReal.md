<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.biasedSignPMF_apply_toReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real Mass of a Biased Sign

**Claim.** For every $p\in[0,1]$ and every sign $x\in\{\pm1\}$, the real-valued mass of $x$ under the biased sign distribution is $1-p$ if $x=+1$, and is $p$ otherwise.

**Proof.** There are two possible signs. For $x=1$, the mass is the keep probability at mean bias $1-2p$, namely $(1+(1-2p))/2=1-p$. For $x=-1$, the mass is its complement. Converting this complementary extended-real mass to a real number is valid because the keep probability is at most one; it gives $1-(1+(1-2p))/2=p$. These two cases yield the stated formula.

**Key facts.** `FABL.biasMean_mem_Icc`, `FABL.biasedSignPMF_apply_one`, `FABL.biasedSignPMF_apply_neg_one`, `FABL.correlationKeepProbability_le_one`.
