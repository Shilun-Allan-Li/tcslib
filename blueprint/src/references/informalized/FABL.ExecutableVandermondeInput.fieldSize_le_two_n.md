<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableVandermonde.lean :: FABL.ExecutableVandermondeInput.fieldSize_le_two_n -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Field size upper bound

**Claim.** For the defined degree $d$, one has $2^d\le 2n$.

**Proof.** If $n=1$, then $d=1$ and the result is the equality $2=2n$. Otherwise, positivity of $n$ gives $1<n$. Thus $\lceil\log_2 n\rceil=\operatorname{Nat.clog}(2,n)$ is positive, so the maximum defining $d$ equals this ceiling. The predecessor property of the ceiling gives $2^{d-1}<n$ (\texttt{Nat.pow_pred_clog_lt_self}). Since $d=(d-1)+1$, we have $2^d=2^{d-1}\cdot2\le n\cdot2=2n$. Positivity of $n$ used here follows from $1\le k\le n$ (\texttt{ExecutableVandermondeInput.n_pos}).

**Key facts.** `FABL.ExecutableVandermondeInput.n_pos`.
