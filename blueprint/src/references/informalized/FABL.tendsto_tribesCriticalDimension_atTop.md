<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.tendsto_tribesCriticalDimension_atTop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Critical Tribes Dimension Diverges

**Claim.** The tribes critical dimension tends to infinity as the width parameter $w$ tends to infinity.

**Proof.** The critical dimension is asymptotically equivalent to $M_w=(\log 2)w2^w$ (\texttt{tribesCriticalDimension\_isEquivalent\_main}). As $w\to\infty$, both $w$ and $2^w$ tend to infinity, and $\log 2>0$, so their product $M_w$ tends to infinity. Asymptotically equivalent sequences have the same tendency to infinity; hence the critical dimension tends to infinity.

**Key facts.** `FABL.tribesCriticalDimension_isEquivalent_main`.
