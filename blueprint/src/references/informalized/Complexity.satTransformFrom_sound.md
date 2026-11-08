<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satTransformFrom_sound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Soundness of the threaded transform

**Claim.** If the formula produced by the threaded clause transform is satisfied, then the original formula is satisfied by the same assignment.

**Proof.** Induct on the list of clauses. The empty formula is satisfied. For a clause $C$ followed by a tail, satisfaction of the concatenation of the transformed pieces means that the clauses produced from $C$ and the recursively transformed tail are both satisfied. The clause-splitting soundness result says that satisfaction of the first piece implies satisfaction of $C$ (`Complexity.satSplitClause_sound`). The induction hypothesis turns satisfaction of the transformed tail into satisfaction of the original tail. Together these give satisfaction of the original formula.

**Key facts.** `Complexity.satSplitClause_sound`.
