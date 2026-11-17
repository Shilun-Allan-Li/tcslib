<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.natCard_partitePerfectMatching_le_doubleFactorial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Partite matching double factorial bound

**Claim.** For natural numbers $r$ and $k$, the number of partite perfect matching codes with parameters $2r$ and $k$ is at most $(2rk-1)!!$.

**Proof.** First forget the partite condition. The partite-code count is at most the count of all perfect matching codes with parameter $((2r)k)/2$ (\texttt{natCard_partitePerfectMatching_le_code}). The number of codes with parameter $m$ is $(2m-1)!!$ (\texttt{natCard_perfectMatchingCode}), so this gives the bound $(2(((2r)k)/2)-1)!!$. Since $((2r)k)/2=rk$, the expression simplifies to $(2rk-1)!!$.

**Key facts.** `FABL.natCard_partitePerfectMatching_le_code`, `FABL.natCard_perfectMatchingCode`.
