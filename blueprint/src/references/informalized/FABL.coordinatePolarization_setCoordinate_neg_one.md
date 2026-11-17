<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.coordinatePolarization_setCoordinate_neg_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polarization at the negative coordinate

**Claim.** For a sign-valued function $f$, coordinate $i$, and point $x$, its coordinate polarization evaluated after setting coordinate $i$ to $-1$ is the minimum of the values of $f$ at the two points obtained by setting coordinate $i$ to $1$ and to $-1$.

**Proof.** At the point obtained by setting coordinate $i$ to $-1$, the value of coordinate $i$ is not $1$. By the definition of coordinate polarization, this selects the minimum branch, whose two arguments are exactly the values of $f$ at the points with coordinate $i$ set to $1$ and to $-1$.
