<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveNecessity.lean :: FABL.eventually_affine_positive -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Eventual positivity of affine functions

**Claim.** For a finite set $\Omega$, a real number $c$, and a function $X:\Omega\to\mathbb R$, every value $1+ctX(x)$ is positive for all $t$ sufficiently close to $0$.

**Proof.** For each fixed $x\in\Omega$, the function $t\mapsto 1+ctX(x)$ is continuous at $0$ and has value $1$ there. Since the positive reals form a neighborhood of $1$, this function is positive whenever $t$ is sufficiently close to $0$. There are only finitely many $x$, so the intersection of these neighborhoods of $0$ is again a neighborhood of $0$. Thus all the inequalities hold simultaneously.
