<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/ModThree.lean :: FABL.abs_fourierCoeff_modThree_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mod-three Fourier coefficient bound

**Claim.** For every nonempty coordinate set $S$, the absolute value of the mod-three Fourier coefficient is at most $\frac23(\frac{\sqrt3}{2})^n$.

**Proof.** Use the formula for the coefficient at a nonempty set (`fourierCoeff_modThree_of_nonempty`). If $|S|$ is odd, the coefficient is zero and the bound follows from nonnegativity of the right-hand side. If $|S|$ is even, taking absolute values in that formula leaves $\frac23(\frac12)^n(\sqrt3)^{|S|}$, since the remaining factors are signs. Because $|S|\leq n$ and $\sqrt3\geq1$, this is at most $\frac23(\frac12)^n(\sqrt3)^n=\frac23(\frac{\sqrt3}{2})^n$.

**Key facts.** `FABL.fourierCoeff_modThree_of_nonempty`.
