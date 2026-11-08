<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLCounterexample.lean :: FABL.normalizedRademacherSum_setCoordinate_sub -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Changing One Coordinate

**Claim.** For every natural number $n$, coordinate $i$, and sign vector $x$, the normalized sum with coordinate $i$ set to $1$ minus the normalized sum with that coordinate set to $-1$ equals $2(\sqrt n)^{-1}$.

**Proof.** Write each of the two sums using the same constant coefficient and subtract them term by term. At every coordinate other than $i$, the updated vectors agree, so those differences vanish. At coordinate $i$, the sign values are $1$ and $-1$, respectively; their difference is $2$. Multiplying by the coefficient $(\sqrt n)^{-1}$ gives the stated result.
