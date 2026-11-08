<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.natCard_partitePerfectMatching_le_factorial_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Partite matching factorial bound

**Claim.** If $r>0$, then the number of partite perfect matching codes with parameters $2r$ and $k$, viewed as a real number, is at most $\left(\frac{2r-1}{r}\right)^{rk}((rk)!)^2$.

**Proof.** Put $m=rk$. The double-factorial bound for partite codes, together with the inequality $(2m-1)!!\le (m!)^2$ (\texttt{natCard_partitePerfectMatching_le_doubleFactorial} and \texttt{oddDoubleFactorial_le_factorial_sq}), shows that the code count is at most $(m!)^2$. The index in the double factorial is $2m-1$, since $2rk-1=2m-1$. Because $r>0$, the ratio $(2r-1)/r$ is at least $1$: this is equivalent to $r\le 2r-1$. Its $m$th power is therefore at least $1$. Multiplying the factorial-square bound by this factor can only increase it, yielding the claimed bound after substituting $m=rk$.

**Key facts.** `FABL.natCard_partitePerfectMatching_le_doubleFactorial`, `FABL.oddDoubleFactorial_le_factorial_sq`.
