<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.canonicalParityCircuit_size_real_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonical parity circuit size bound

**Claim.** For all natural numbers $n,q$, the canonical parity depth circuit with block side $\max(1,\lceil n^{1/(q+2)}\rceil)$ has size at most $(q+2)(n^{1/(q+2)}+1)^{q+1}2^{n^{1/(q+2)}+1}$.

**Proof.** Write $r$ for the chosen block side and $R=n^{1/(q+2)}$. Since $r\ge1$ (`one_le_parityBlockSide`), the circuit size estimate for block constructions bounds its size by $(q+2)r^{q+1}2^r$ (`size_parityDepthCircuitFromBlocks_le`), and the same inequality holds after casting to real numbers. The ceiling estimate gives $r\le R+1$ (`parityBlockSide_le_root_add_one`). Hence $r^{q+1}\le(R+1)^{q+1}$, and, because the base $2$ is greater than $1$, $2^r\le2^{R+1}$. The factors are nonnegative, so these bounds can be multiplied into the claimed estimate.

**Key facts.** `FABL.one_le_parityBlockSide`, `FABL.size_parityDepthCircuitFromBlocks_le`, `FABL.parityBlockSide_le_root_add_one`.
