<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/FriedgutNecessity.lean :: FABL.card_addressingDataIndicesOutside_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Data Indices Outside a Coordinate Set

**Claim.** If $m>0$ and $J$ is a set of at most $2^{m-1}$ coordinates among the $m+2^m$ coordinates, then at least $2^{m-1}$ indices select data coordinates outside $J$.

**Proof.** Among the $2^m$ indices, the number whose corresponding data coordinate lies in $J$ is at most $|J|$, by the bound on indices landing inside a coordinate set ( `FABL.card_addressingDataIndicesIn_le`). Thus at most $2^{m-1}$ indices land inside. The inside and outside cases partition all indices, so the number outside is at least $2^m-2^{m-1}$. Since $m>0$, we have $2^m=2\cdot 2^{m-1}$, and this lower bound is $2^{m-1}$.

**Key facts.** `FABL.card_addressingDataIndicesIn_le`.
