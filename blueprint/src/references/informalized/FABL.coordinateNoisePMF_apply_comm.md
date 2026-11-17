<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseKernels.lean :: FABL.coordinateNoisePMF_apply_comm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetry of coordinate noise

**Claim.** For $\rho\in[-1,1]$ and signs $x,y$, the coordinate noise probability of moving from $x$ to $y$ equals that of moving from $y$ to $x$.

**Proof.** Every sign is either $1$ or $-1$, so it suffices to check the four possible pairs. The noise rule chooses to keep the input with probability $p=(1+\rho)/2$ and to flip it with probability $1-p$. If the two signs agree, either direction has probability $p$; if they differ, either direction has probability $1-p$. Thus the transition probabilities are symmetric. The bound $p\leq 1$ (`correlationKeepProbability_le_one`) ensures the keep and flip weights define the stated distribution.

**Key facts.** `FABL.correlationKeepProbability_le_one`.
