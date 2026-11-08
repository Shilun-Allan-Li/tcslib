<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/NormalFormConversion.lean :: BoolCircuit.NOrCircuit.clauseToClause_nodup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distinct Indices After Clause Translation

**Claim.** If the variable indices in a Boolean-circuit literal list are pairwise distinct, then the translated clause has no repeated literals.

**Proof.** Apply the corresponding translation result for terms: pairwise distinct variable indices in the input literal list imply that the translated term has no repeated literals (`BoolCircuit.NAndCircuit.clauseToTerm_nodup`). The clause translation sends each input literal to the same variable with its sign converted, just as the term translation does; this identifies the resulting lists, so the translated clause is also duplicate-free.

**Key facts.** `BoolCircuit.NAndCircuit.clauseToTerm_nodup`.
