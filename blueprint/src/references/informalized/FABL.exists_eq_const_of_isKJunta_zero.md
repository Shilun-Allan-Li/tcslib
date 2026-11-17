<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.exists_eq_const_of_isKJunta_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-Juntas Are Constant

**Claim.** If a sign-valued function on the Boolean cube depends on at most zero coordinates, then it is identically equal to some sign.

**Proof.** The zero-junta hypothesis provides a set $J$ of at most zero coordinates on which the function depends. Thus $|J|=0$, so $J$ is empty. Fix the all-$1$ input $x_0$ and take the value $f(x_0)$. For any input $x$, the two inputs agree on every coordinate in $J$, vacuously because $J$ is empty. Dependence only on $J$ therefore implies $f(x)=f(x_0)$.
