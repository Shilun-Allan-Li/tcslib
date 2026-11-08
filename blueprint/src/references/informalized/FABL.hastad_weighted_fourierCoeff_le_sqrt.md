<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadTests.lean :: FABL.hastad_weighted_fourierCoeff_le_sqrt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weighted Fourier Coefficient Bound

**Claim.** Under the stated hypotheses, every odd-cardinality set $S$ satisfies $(1-\delta)^{|S|}\widehat f(S)\le\sqrt{\varepsilon}$.

**Proof.** Because $|S|$ is odd, $S$ is nonempty; choose a coordinate $i\in S$. Put $\rho=1-\delta$. The parameter bounds give $0\le\rho\le1$ and $\rho\le1-\varepsilon$. Since $|S|\ge1$, these imply $\rho^{2|S|}\le\rho^{|S|-1}\le(1-\varepsilon)^{|S|-1}$. Squaring the target expression and using this power comparison gives
\[
\bigl(\rho^{|S|}\widehat f(S)\bigr)^2\le (1-\varepsilon)^{|S|-1}\widehat f(S)^2.
\]
The right side is one term in the stable influence at coordinate $i$, so it is at most that influence (`stableInfluence_term_le`), which by hypothesis is at most $\varepsilon$. Thus the square of the target expression is at most $\varepsilon$. Since $\varepsilon\ge0$, its absolute value is at most $\sqrt{\varepsilon}$; in particular, the expression itself is at most $\sqrt{\varepsilon}$.

**Key facts.** `FABL.stableInfluence_term_le`.
