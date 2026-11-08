<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.hammingDist_add_single_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distance after one coordinate change

**Claim.** For every $n\ge 0$, vector $x\in\mathbb F_2^n$, coordinate $i$, and $c\in\mathbb F_2$, adding $c$ at coordinate $i$ changes at most one coordinate, so the Hamming distance is at most $1$.

**Proof.** The Hamming distance counts the coordinates where the two vectors differ. If $j\ne i$, the vector supported at $i$ vanishes at $j$, so adding it leaves the $j$th coordinate unchanged. Therefore every coordinate where $x$ differs from $x+\operatorname{single}(i,c)$ must be $i$. The set of differing coordinates is contained in the singleton $\{i\}$, whose size is $1$.
