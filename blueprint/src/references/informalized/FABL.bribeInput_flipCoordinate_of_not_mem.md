<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.bribeInput_flipCoordinate_of_not_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bribing Commutes with an Outside Flip

**Claim.** If $i\notin J$, flipping coordinate $i$ before bribing the coordinates in $J$ gives the same input as bribing first and then flipping coordinate $i$.

**Proof.** Compare coordinates $j$. If $j\in J$, then $j\ne i$ because $i\notin J$; the flip does not affect that coordinate, and bribing sets it to $b$ on either side. If $j=i$, it is outside $J$, so bribing retains its value, and both sides use the flipped value $-x(i)$. If $j$ is neither in $J$ nor equal to $i$, neither operation changes it. Thus the resulting vectors agree coordinatewise.
