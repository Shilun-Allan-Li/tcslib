<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/FriedgutNecessity.lean :: FABL.not_close_addressing_of_isKJunta -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Addressing Function Distance from Juntas

**Claim.** For positive $m$, every Boolean function depending on at most $2^{m-1}$ coordinates has relative Hamming distance at least $1/4$ from the addressing function on $m+2^m$ inputs.

**Proof.** By the definition of being a $2^{m-1}$-junta, there is a coordinate set $J$ of size at most $2^{m-1}$ on which $g$ depends. Apply the addressing-function distance bound (`relativeHammingDist_addressing_ge_quarter`) to this $J$, the given function $g$, and its dependence on $J$. It gives the required lower bound of $1/4$.

**Key facts.** `FABL.relativeHammingDist_addressing_ge_quarter`.
