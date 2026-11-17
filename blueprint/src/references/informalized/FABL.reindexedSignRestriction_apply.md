<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.reindexedSignRestriction_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a Reindexed Sign Restriction

**Claim.** For every sign vector $x$ of dimension $|J|$, the reindexed sign restriction equals $f$ evaluated on the full sign vector formed from the corresponding signs on $J$ and the fixed signs outside $J$.

**Proof.** Unfolding the reindexed restriction gives the sign restriction evaluated at the assignment on $J$ whose value at $i$ is the coordinate of $x$ indexed by the equivalence between $J$ and its finite reindexing. The sign restriction itself evaluates $f$ on the full sign vector obtained by combining that assignment with the fixed signs outside $J$. This is exactly the stated expression.
