<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.parityTreeAssignment_zero_eq_blockValue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial parity tree assignment

**Claim.** At level zero, the parity tree assignment at group index $g$ agrees coordinatewise with the block assignment: coordinate $j$ is $x_{gr+j}$ when $gr+j<n$, and is $1$ otherwise.

**Proof.** Fix a coordinate $j$. By definition, the level-zero assignment at coordinate $j$ is the parity tree value at index $gr+j$. The depth-zero value is the padded input at that index, which is $x_{gr+j}$ if the index is below $n$ and $1$ otherwise. This is exactly the corresponding coordinate of the block assignment, so the two functions agree at every coordinate.
