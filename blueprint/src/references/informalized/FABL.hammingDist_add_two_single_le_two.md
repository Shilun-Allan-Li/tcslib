<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.hammingDist_add_two_single_le_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distance after two coordinate changes

**Claim.** For every $n\ge 0$, vector $x\in\mathbb F_2^n$, and coordinates $i,j$, adding $1$ at both coordinates changes at most two coordinates, so the Hamming distance is at most $2$.

**Proof.** The Hamming distance counts the coordinates where the vectors differ. At any coordinate outside $\{i,j\}$, both added single-coordinate vectors vanish, so the sum leaves $x$ unchanged there. Thus the set of differing coordinates is contained in $\{i,j\}$. This set has at most two elements, including when $i=j$, and the claimed bound follows.
