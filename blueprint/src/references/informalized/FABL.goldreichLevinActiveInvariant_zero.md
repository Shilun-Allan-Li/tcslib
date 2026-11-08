<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/Controller.lean :: FABL.goldreichLevinActiveInvariant_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Active Invariant

**Claim.** At stage zero, the family consisting only of the empty frequency set satisfies the active invariant.

**Proof.** Check the invariant's three clauses. The only member of the family is the empty set, which is contained in the empty prefix. Every frequency set has empty length-zero prefix, so that prefix belongs to the family. Finally, the third clause requires a hypothesis that the stage is positive; at stage zero this cannot hold, so the clause is vacuous.
