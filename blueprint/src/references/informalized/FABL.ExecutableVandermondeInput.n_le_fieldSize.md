<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableVandermonde.lean :: FABL.ExecutableVandermondeInput.n_le_fieldSize -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dimension is at most field size

**Claim.** For the defined degree $d$, one has $n\le 2^d$.

**Proof.** By the defining property of the ceiling logarithm, $n\le 2^{\operatorname{Nat.clog}(2,n)}$ (\texttt{Nat.le_pow_clog}). Also $\operatorname{Nat.clog}(2,n)\le d$, since $d$ is the maximum of $1$ and that ceiling. Monotonicity of powers of $2$ therefore gives $2^{\operatorname{Nat.clog}(2,n)}\le2^d$, and combining the inequalities proves the claim.
