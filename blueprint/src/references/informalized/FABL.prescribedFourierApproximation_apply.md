<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PrescribedFourierSupport.lean :: FABL.prescribedFourierApproximation_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prescribed Fourier approximation decomposition

**Claim.** The prescribed Fourier approximation at $x$ equals the real value of $f$ at $x$ plus the sum of the off-center contributions from all other points of the cube.

**Proof.** View the approximation as a sum over every point $a$ of the cube, and split off the term with $a=x$. The remaining terms are exactly the off-center sum. On the diagonal, the prescribed Fourier kernel equals $1$ (by the diagonal identity, `prescribedFourierKernel_apply_self`), so the removed term is the real value of $f(x)$. Combining these two parts gives the stated decomposition.

**Key facts.** `FABL.prescribedFourierKernel_apply_self`.
