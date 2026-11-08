<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableVandermonde.lean :: FABL.ExecutableVandermondeInput.fieldDegree_succ_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Field degree upper bound

**Claim.** For the defined degree $d$, one has $d+1\le 4(n+1)$.

**Proof.** Every natural number $\ell$ satisfies $\ell+1\le 2^{\ell+1}$ (\texttt{nat_succ_le_two_pow_succ}). Apply this with $\ell=d$. Since $2^d\le 2n$ (\texttt{fieldSize_le_two_n}), multiplying by $2$ gives $2^{d+1}=2\cdot 2^d\le 4n$. Hence $d+1\le 4n\le 4(n+1)$, proving the stated bound.

**Key facts.** `FABL.nat_succ_le_two_pow_succ`, `FABL.ExecutableVandermondeInput.fieldSize_le_two_n`.
