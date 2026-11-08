<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/FriedgutNecessity.lean :: FABL.sensitivity_addressingFunction_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Addressing Function Sensitivity Bound

**Claim.** For every address length $m$ and every input to the addressing function, its sensitivity is at most $m+1$.

**Proof.** Every coordinate whose flip changes the output belongs to the set of relevant coordinates (`isPivotal_addressingFunction_mem_relevant`). Thus the pivotal-coordinate set is contained in the relevant-coordinate set, so its cardinality, which is the sensitivity, is no larger than the cardinality of the relevant-coordinate set. That latter cardinality is at most $m+1$ (`card_addressingRelevantCoordinates_le`), giving the result.

**Key facts.** `FABL.isPivotal_addressingFunction_mem_relevant`, `FABL.card_addressingRelevantCoordinates_le`.
