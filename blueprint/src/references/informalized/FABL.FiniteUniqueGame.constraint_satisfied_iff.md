<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.FiniteUniqueGame.constraint_satisfied_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constraint Satisfaction Criterion

**Claim.** A constraint with source $u$, target $v$, and attached permutation $\pi_e$ is satisfied exactly when $\pi_e$ sends the label of $v$ to the label of $u$.

**Proof.** The associated predicate evaluates to the Boolean decision of the equality $\pi_e(\ell(v))=\ell(u)$. A Boolean decision equals true exactly when the proposition being decided holds, which is the stated criterion.
