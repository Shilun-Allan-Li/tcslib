<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/NormalFormConversion.lean :: BoolCircuit.NAndCircuit.toCNF_clauses_nodup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distinct Literals in CNF Clauses

**Claim.** If every input clause circuit has pairwise distinct variable indices, then every clause in the CNF of their AND-node has no repeated literal.

**Proof.** A clause in the CNF of the AND-node arises by mapping a member $c$ of the list of clause circuits to its clause representation. By hypothesis, that member is a base clause whose list of literal indices has no repetitions. The clause conversion preserves this distinctness (`BoolCircuit.NOrCircuit.clauseToClause_nodup`), so the resulting clause has no repeated literal.

**Key facts.** `BoolCircuit.NOrCircuit.clauseToClause_nodup`.
