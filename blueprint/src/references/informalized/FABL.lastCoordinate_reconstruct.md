<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/NoiseOperatorExercises.lean :: FABL.lastCoordinate_reconstruct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reconstruction from the last coordinate

**Claim.** For a function on the $(n+1)$-dimensional Boolean cube, its value at $(x,a)$ is the even part at $x$ plus $a$ times the odd part at $x$.

**Proof.** The last coordinate $a$ is either $1$ or $-1$. If $a=1$, the average of the two endpoint values plus their half-difference is the value at $1$. If $a=-1$, subtracting the half-difference from the average gives the value at $-1$. Since $a$ equals its real sign value in both cases, these identities are exactly $f(x,a)=f_{\mathrm{even}}(x)+a f_{\mathrm{odd}}(x)$.
