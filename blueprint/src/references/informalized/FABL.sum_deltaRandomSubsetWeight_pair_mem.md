<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.sum_deltaRandomSubsetWeight_pair_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weight of subsets containing a pair

**Claim.** For coordinates $i,j$, the total weight of subsets containing both is $\delta$ if $i=j$ and $\delta^2$ if $i\ne j$.

**Proof.** Split into the cases $i=j$ and $i\ne j$. If they are equal, the condition is simply that the subset contain $i$; the total weight of supersets of $\{i\}$ is $\delta^{|\{i\}|}=\delta$ (`FABL.sum_deltaRandomSubsetWeight_supset`). If they are distinct, containing both is equivalent to containing $\{i,j\}$, whose size is two. The same supersets identity gives total weight $\delta^2$.

**Key facts.** `FABL.sum_deltaRandomSubsetWeight_supset`.
