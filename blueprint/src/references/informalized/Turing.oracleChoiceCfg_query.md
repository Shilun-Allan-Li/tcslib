<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleChoiceCfg_query -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Invariance of the query string

**Claim.** Inserting a new tape in the designated oracle-choice slot leaves the query string unchanged.

**Proof.** The query string is determined solely by the contents function of the query tape. The query tape occupies the last slot among the original tapes, and after inserting the choice tape, the corresponding original slot is still the last slot among the enlarged configuration's original tapes. Insertion therefore leaves the contents function at that slot unchanged (`Fin.insertNth_apply_succAbove`). Since the two query-tape contents functions agree at every integer cell, the definition of query string gives the same string for both configurations.
