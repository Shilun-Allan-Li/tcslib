<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/P.lean :: Complexity.mem_P_of_dtime_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Bound Implies Membership

**Claim.** If $L\in\mathrm{DTIME}(T)$ and $T(n)\le c(n^d+1)$ for all $n$, then $L\in\mathsf{P}$.

**Proof.** Choose a machine witnessing $L\in\mathrm{DTIME}(T)$, with time multiplier $a$. On an input $x$, its time bound is $aT(|x|)$, which is at most $ac(|x|^d+1)$ by the assumed pointwise bound. Thus the same machine witnesses membership in $\mathrm{DTIME}(n\mapsto n^d+1)$, with multiplier $ac$; the monotonicity of computation time allows the larger bound. This polynomial-time class is contained in $\mathsf{P}$ (`Complexity.dtime_poly_subset_P`), proving the result.

**Key facts.** `Complexity.dtime_poly_subset_P`, `Turing.FinTM.ComputesInTime.mono`.
