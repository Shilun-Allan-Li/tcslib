<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.normalizeParityBlockAssignment_eq_self -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Normalization Preserves Valid Assignments

**Claim.** If an assignment has value $1$ whenever $n\le gr+j$, then normalizing it leaves the assignment unchanged.

**Proof.** Fix an index $j$. If $gr+j<n$, normalization retains the original value at $j$. Otherwise $n\le gr+j$, so validity says the original value is $1$; normalization also assigns $1$ there. Thus the two assignments agree at every index.
