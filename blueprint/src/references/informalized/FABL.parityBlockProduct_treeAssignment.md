<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.parityBlockProduct_treeAssignment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product of a parity tree assignment

**Claim.** The product of the signs assigned by the parity tree at level $t$ to the block starting at $gr$ equals the parity tree value at level $t+1$ and index $g$.

**Proof.** By definition, the block assignment at position $j$ is the parity tree value at level $t$ and index $gr+j$. The product of all signs in this assignment is therefore exactly the defining product for the parity tree value at level $t+1$ and index $g$.
