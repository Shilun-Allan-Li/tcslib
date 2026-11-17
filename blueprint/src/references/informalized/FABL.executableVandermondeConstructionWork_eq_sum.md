<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableVandermonde.lean :: FABL.executableVandermondeConstructionWork_eq_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vandermonde construction work as a sum

**Claim.** For natural numbers $k$ and $n$, the executable Vandermonde construction work is the field preprocessing work at $\ell=\max(1,\lceil\log_2 n\rceil)$ plus $n$ times one plus the sum, over $q=0,\ldots,k-2$, of the power work at exponent $q+1$ together with $\ell+1$.

**Proof.** First rewrite the construction work using its traversal formula: it is the field preprocessing work plus $n$ times one more than the work for the first $k-1$ power rows (\texttt{FABL.executableVandermondeConstructionWork_eq}). The power-row work is the sum, over $q$ in the range from $0$ to $k-2$, of the power work at exponent $q+1$ together with $\ell+1$ (\texttt{FABL.executableVandermondePowerRowsWork_eq_sum}). Substituting this sum gives the claimed expression.

**Key facts.** `FABL.executableVandermondeConstructionWork_eq`, `FABL.executableVandermondePowerRowsWork_eq_sum`.
