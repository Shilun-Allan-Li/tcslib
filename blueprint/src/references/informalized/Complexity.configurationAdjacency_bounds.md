<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.configurationAdjacency_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Configuration Adjacency Formula Bounds

**Claim.** For a finite-state Turing machine $M$ with $k$ work tapes, under the stated coefficient bound, the adjacency formula has at most $2C(s+n+1)$ variables and its binary serialization has length at most $(5(6+D)+1)C^2(s+n+2)^{k+3}$, with $D$ the transition coefficient specified in the statement.

**Proof.** Every literal in the combined input-equality and transition CNF has a relabeled wire index below $2C(s+n+1)$ (`Complexity.codecPairWire_lt`). The general variable-count bound for a relabeled CNF (`Complexity.codecCnf_numVars`) gives the first estimate. For serialization, the general cost bound (`Complexity.codecAdjacency_cost`) bounds the CNF cost by $(6+D)C(s+n+2)^{k+2}$, and the serialization lemma (`Complexity.codecCnf_serialize`) multiplies this by the number of wires plus three and adds one. Since $2C(s+n+1)+3\le5C(s+n+2)$, the product is at most $5(6+D)C^2(s+n+2)^{k+3}+1$. Finally, $1\le C^2(s+n+2)^{k+3}$, yielding the claimed factor $5(6+D)+1$.

**Key facts.** `Complexity.codecPairWire_lt`, `Complexity.codecCnf_numVars`, `Complexity.codecAdjacency_cost`, `Complexity.codecCnf_serialize`.
