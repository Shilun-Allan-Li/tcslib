<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPoly.lean :: Randomized.PolyAmp.runVal_two_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower Bound for the Run Value

**Claim.** If a uniformly random length-$K$ choice word is accepted with probability at least $2/3$, then the rejecting-rule run value with $K+1$ blocks, parameter $K$, and initial count zero is at least $1-2(8/9)^{\lfloor(K+1)/2\rfloor}$.

**Proof.** Let $B$ indicate rejection on a length-$K$ block. Its probability is at most $1/3=1/2-1/6$, since rejection is the complement of acceptance. The tail bound for block counts, with $K+1$ blocks and $\varepsilon=1/6$, shows that the probability that at least half the blocks reject is at most $2(1-4(1/6)^2)^{\lfloor(K+1)/2\rfloor}=2(8/9)^{\lfloor(K+1)/2\rfloor}$. If the rejecting decision rule fails, then the number of accepting blocks is at most half the blocks; because accepting and rejecting counts sum to $K+1$, this implies that at least half the blocks reject. Thus failure is contained in the tail event just bounded. The run value is one minus the failure probability, giving the claimed lower bound.

**Key facts.** `Randomized.randProb_congr`, `Randomized.randProb_bool_false`, `Randomized.randProb_tail_le`, `Randomized.blockCount_add_not`, `Randomized.randProb_mono`, `Randomized.randProb_not`.
