<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.CoordRestriction.complete_fixCoordinate_of_free -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completion after fixing a free coordinate

**Claim.** If coordinate $i$ is free in the restriction, then fixing it to a sign $s$ and completing with $x$ gives the same vector as completing the original restriction with the $i$th bit replaced by the binary value corresponding to $s$.

**Proof.** Compare coordinates. At $j\ne i$, neither the restriction update nor the replacement of the $i$th bit changes the data used at $j$, so the completed values agree. At $i$, the updated restriction prescribes the fixed sign $s$. On the other side, the original restriction is free there, and the replacement bit is the binary encoding of $s$; its sign encoding is therefore $s$. Hence the vectors agree at every coordinate.
