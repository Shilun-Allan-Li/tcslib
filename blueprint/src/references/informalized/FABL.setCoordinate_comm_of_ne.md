<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.setCoordinate_comm_of_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Commuting Distinct Coordinate Updates

**Claim.** Replacing two distinct coordinates $i$ and $j$ by $a$ and $b$, respectively, gives the same vector regardless of the order of the replacements.

**Proof.** Compare the two resulting vectors coordinate by coordinate. At coordinate $i$, both have value $a$; at coordinate $j$, both have value $b$. At any other coordinate, neither update changes the original value. Thus the two vectors agree everywhere.
