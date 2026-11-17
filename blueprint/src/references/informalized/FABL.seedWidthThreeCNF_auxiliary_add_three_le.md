<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.seedWidthThreeCNF_auxiliary_add_three_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Auxiliary-variable budget bound

**Claim.** If $3\le r$, then $(r-3)$ times the size of the seed's acceptance CNF, plus $3$, is at most $r2^r$.

**Proof.** The acceptance CNF has size at most $2^r$ (`FABL.seedAcceptanceCNF_size_le`). Since $r-3$ is nonnegative, multiplying this bound by $r-3$ and adding $3$ gives an upper bound of $(r-3)2^r+3$. Also $1\le 2^r$, so $3\le 3\cdot 2^r$. Thus the latter expression is at most $((r-3)+3)2^r=r2^r$, using $r-3+3=r$ from $3\le r$.

**Key facts.** `FABL.seedAcceptanceCNF_size_le`.
