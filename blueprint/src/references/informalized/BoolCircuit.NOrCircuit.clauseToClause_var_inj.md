<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/NormalFormConversion.lean :: BoolCircuit.NOrCircuit.clauseToClause_var_inj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variable Uniqueness in a Translated Clause

**Claim.** For a literal list with pairwise distinct variable indices, any two literals in its translated clause that have the same variable are equal.

**Proof.** Use the corresponding uniqueness result for the translated term: among its literals, equality of variables forces equality of literals (`BoolCircuit.NAndCircuit.clauseToTerm_var_inj`). The clause translation has the same elementwise variable-preserving conversion as the term translation, so its translated list has the same property.

**Key facts.** `BoolCircuit.NAndCircuit.clauseToTerm_var_inj`.
