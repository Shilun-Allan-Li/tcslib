<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.isUnit_f₂Polynomial_iff_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Units in the binary polynomial ring

**Claim.** A polynomial over $\mathbb F_2$ is a unit if and only if it equals the constant polynomial $1$.

**Proof.** If $p$ is a unit, the unit criterion for polynomials over a field says that $p$ is a nonzero constant, say $a$. The field $\mathbb F_2$ has only two elements, $0$ and $1$; since $a$ is nonzero, it must be $1$. Thus $p=1$. Conversely, $1$ is a unit, so any polynomial equal to $1$ is a unit.
