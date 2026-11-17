<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityLimits.lean :: FABL.hasDerivAt_arcsinSeriesTerm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of an arcsine series term

**Claim.** For every natural number $j$ and real number $z$, the function $y\mapsto c_j y^{2j+1}$ has derivative $\frac{\binom{2j}{j}}{2^{2j}}z^{2j}$ at $z$, where $c_j=\frac{\binom{2j}{j}}{2^{2j}(2j+1)}$.

**Proof.** The power rule gives derivative $(2j+1)c_j z^{2j}$ for this constant multiple of a monomial. By the definition of $c_j$, the scalar $(2j+1)c_j$ simplifies to $\binom{2j}{j}/2^{2j}$. Substitution yields the claimed derivative.
