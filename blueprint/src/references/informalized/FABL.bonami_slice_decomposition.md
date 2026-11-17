<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Reasonableness.lean :: FABL.bonami_slice_decomposition -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First-coordinate slice decomposition

**Claim.** For a real-valued function $f$ on the $(n+1)$-dimensional sign cube, a sign $b$, and a point $x$ in the $n$-dimensional sign cube, the value at $(b,x)$ is $b$ times the odd part at $x$ plus the even part at $x$.

**Proof.** A sign $b$ is either $1$ or $-1$. If $b=1$, the odd and even parts are respectively half the difference and half the sum of the two slices; adding them gives the slice at $1$. If $b=-1$, subtracting the odd part from the even part gives the slice at $-1$. Since the sign value of $b$ is the corresponding real number $1$ or $-1$, these two identities give the claimed decomposition.
