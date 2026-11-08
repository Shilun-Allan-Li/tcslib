<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satTransformFrom_width -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width bound for the threaded transform

**Claim.** For every CNF formula and cursor, the formula produced by the threaded clause transform has width at most three.

**Proof.** Induct on the clause list. The empty list produces an empty formula, which meets the width bound. In the cons case, every clause in the concatenated output belongs either to the output of splitting the first clause or to the recursively transformed tail. Clauses in the first part have length at most three by the clause-splitting width bound (`Complexity.satSplitClause_width`); clauses in the tail have length at most three by the induction hypothesis, applied at the cursor returned by the first split. Hence every output clause has length at most three.

**Key facts.** `Complexity.satSplitClause_width`.
