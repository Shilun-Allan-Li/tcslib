<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.bribeFunction_majority_head_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Majority After Head Bribing

**Claim.** Bribing the first $k$ coordinates of majority to $b$ yields the threshold sign of $kb$ plus the sum of the last $m$ coordinates of the input.

**Proof.** Expand the majority function and the bribe: its threshold is applied to the sum of all $k+m$ coordinate signs after the first $k$ coordinates have been replaced by $b$. Decompose the sum over the disjoint first and last coordinate blocks using the equivalence between indices in the concatenated vector and the two summand index sets. Each of the first $k$ summands is then $b$, contributing $k b$. For each index in the last block, the bribe leaves the original coordinate unchanged, and the split equivalence identifies it with the corresponding coordinate of the second component of the input. The total threshold argument is therefore $kb$ plus the sum of that second component, which is exactly the defining argument of majority after head bribing.
