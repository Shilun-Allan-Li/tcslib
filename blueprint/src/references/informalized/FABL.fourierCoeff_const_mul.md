<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/SmallSetExpansion.lean :: FABL.fourierCoeff_const_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scaling Fourier Coefficients

**Claim.** For an integer $n\ge 0$, a real-valued function $f$ on the $n$-dimensional sign cube, a real constant $c$, and a subset $S$ of the coordinates, the Fourier coefficient of $x\mapsto c f(x)$ at $S$ is $c$ times the Fourier coefficient of $f$ at $S$.

**Proof.** Expand the defining integrand as $(c f(x))\chi_S(x)=c(f(x)\chi_S(x))$, using associativity and commutativity of real multiplication. The constant $c$ is independent of the cube point, so it factors out of the finite expectation. The remaining expectation is the Fourier coefficient of $f$ at $S}.
