<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevinAlgorithm/Adaptive.lean :: FABL.goldreichLevinInitialQueryState_satisfiesInvariant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial query state invariant

**Claim.** The initial state, with active family consisting of the empty set and empty trace, satisfies the invariant at stage zero, and its active family has size at most the active cap.

**Proof.** Choose the active family to be the singleton containing the empty set; this is exactly the family stored by the initial state. The stage-zero invariant holds for this family by `goldreichLevinActiveInvariant_zero`: its members lie in the empty prefix, every heavy set has the required zero-coordinate restriction in the family, and the positive-stage weight condition is vacuous at stage zero. The singleton has cardinality one. Since the active cap is positive (`goldreichLevinActiveCap_pos`), its cardinality is at most that cap.

**Key facts.** `FABL.goldreichLevinActiveInvariant_zero`, `FABL.goldreichLevinActiveCap_pos`.
