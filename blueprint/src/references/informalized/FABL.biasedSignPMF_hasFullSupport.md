<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.biasedSignPMF_hasFullSupport -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Full Support of the Biased Sign Distribution

**Claim.** For every $p\in(0,1)$, the biased sign distribution assigns nonzero mass to every sign in $\{\pm1\}$.

**Proof.** Suppose some sign had mass zero. Its real-valued mass would then also be zero. If the sign is $1$, the real-mass formula gives $1-p=0$, contradicting $p<1$. If the sign is $-1$, that formula gives $p=0$, contradicting $p>0$. Since these exhaust the signs, every sign has nonzero mass.

**Key facts.** `FABL.biasedSignPMF_apply_toReal`.
