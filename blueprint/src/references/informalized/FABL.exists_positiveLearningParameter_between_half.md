<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/Program.lean :: FABL.exists_positiveLearningParameter_between_half -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rational learning parameter approximation

**Claim.** For every positive real number $x$, there is a rational $q$ with $0<q\leq\tfrac12$ that lies strictly between half of $\min\{x,\tfrac12\}$ and $\min\{x,\tfrac12\}$.

**Proof.** Set $m=\min\{x,\tfrac12\}$. Since both entries in the minimum are positive, $m>0$, so $m/2<m$. The density of the rationals in the reals gives a rational $q$ with $m/2<q<m$. In particular $q>0$, and since $m\leq\tfrac12$, also $q<\tfrac12$, hence $q\leq\tfrac12$. Thus $q$ has the required bounds.
