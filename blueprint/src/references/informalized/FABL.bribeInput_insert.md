<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.bribeInput_insert -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bribing an Inserted Coordinate

**Claim.** Replacing coordinates in $J\cup\{i\}$ by $b$ gives the same vector as first setting coordinate $i$ to $b$ and then replacing coordinates in $J$ by $b$.

**Proof.** Compare the two vectors at a coordinate $j$. If $j=i$, both sides assign it the value $b$. If $j\ne i$, membership of $j$ in $J\cup\{i\}$ is equivalent to membership in $J$, and setting coordinate $i$ leaves coordinate $j$ unchanged (`setCoordinate_apply_of_ne`). Thus both sides give $b$ when $j\in J$ and otherwise retain $x(j)$. Equality at every coordinate proves the vector identity.

**Key facts.** `FABL.setCoordinate_apply_of_ne`.
