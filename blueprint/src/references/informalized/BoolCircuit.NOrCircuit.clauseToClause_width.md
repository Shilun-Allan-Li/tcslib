<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/NormalFormConversion.lean :: BoolCircuit.NOrCircuit.clauseToClause_width -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width of a Translated Clause

**Claim.** The width of the translated clause equals the length of the original literal list.

**Proof.** For a clause constructor, translation maps each input literal to one output literal. Consequently the translated list has the same length as the input list. Since width is defined as list length, the two quantities are equal.
