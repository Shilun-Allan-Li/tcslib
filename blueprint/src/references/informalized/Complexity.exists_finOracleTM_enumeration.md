<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/Relativization.lean :: Complexity.exists_finOracleTM_enumeration -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Enumeration of Finite Oracle Machines

**Claim.** There is a sequence of finite binary oracle machines in which every finite binary oracle machine has an equivalent machine at an index at least any prescribed lower bound, with equivalence holding for all oracles, inputs, outputs, and time bounds.

**Proof.** Fix a finite oracle machine $M$ and a lower bound $i_0$. Relabel its finite state set by the standard finite set of the same cardinality. The relabeled transition table remains well formed (`oracleRelabel_wellFormed`) and computes the same outputs within every exact time bound for every oracle (`oracleRelabel_computesInTime`). Encode this canonical table as an index $j$ in the enumeration. The decoding property `decodeOracleTable_rank` says that decoding $j$ recovers exactly the canonical machine with that table. Choose the final index to be the pairing of $j$ with $i_0$. The enumeration's pairing property (`oracleEnumeration_pair`) decodes this index to the machine at $j$, while the pairing function guarantees the final index is at least $i_0$. The relabeling equivalence then proves the required exact-time computational equivalence for every oracle, input, output, and time.

**Key facts.** `Complexity.oracleRelabel_wellFormed`, `Complexity.decodeOracleTable_rank`, `Complexity.oracleEnumeration_pair`, `Complexity.oracleRelabel_computesInTime`.
