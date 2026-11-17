<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/FriedgutNecessity.lean :: FABL.uniformProbability_addressingSelectedOutside_ge_half -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower bound for selecting outside a coordinate set

**Claim.** If $m>0$ and $J$ has at most $2^{m-1}$ coordinates, then the probability that the address-selected data coordinate lies outside $J$ is at least $1/2$.

**Proof.** The probability is the fraction of data coordinates outside $J$ (\texttt{FABL.uniformProbability_addressingSelectedOutside}). Since there are $2^m$ data coordinates and at most $2^{m-1}$ members of $J$ in total, at least $2^{m-1}$ data coordinates lie outside $J$ (\texttt{FABL.card_addressingDataIndicesOutside_ge}). Thus the fraction is at least $2^{m-1}/2^m=1/2$, using $m>0$ to write $2^m=2\cdot2^{m-1}$.

**Key facts.** `FABL.uniformProbability_addressingSelectedOutside`, `FABL.card_addressingDataIndicesOutside_ge`.
