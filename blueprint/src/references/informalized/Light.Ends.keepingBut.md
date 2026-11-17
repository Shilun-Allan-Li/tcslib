<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Assigns.lean :: Light.Ends.keepingBut -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation Outside a Chosen Local Set

**Claim.** If the chosen list contains every local assigned by the statement, a bounded execution can end in a state satisfying $Q$ while preserving every local outside that list.

**Proof.** First apply the preservation-of-unassigned-locals result (`Light.Ends.keeping`). This gives a bounded execution whose final state satisfies $Q$ and agrees with the initial state at every index outside the statement's assignment list. Keep the same execution and cost, and enlarge the postcondition using monotonicity (`Light.Ends.mono`) with unchanged budget. If an index lies outside the chosen list, it cannot lie in the assignment list, since that list is contained in the chosen one. Thus the agreement already obtained applies to every such index.

**Key facts.** `Light.Ends.keeping`, `Light.Ends.mono`.
