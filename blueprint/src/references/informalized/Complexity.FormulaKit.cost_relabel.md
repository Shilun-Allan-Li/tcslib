<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/FormulaKit/Gate.lean :: Complexity.FormulaKit.cost_relabel -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cost Invariance Under Relabeling

**Claim.** For any types $\alpha,\beta$, CNF formula $\varphi$ over $\alpha$, and map $f:\alpha\to\beta$, relabeling the variables by $f$ preserves the cost of $\varphi$.

**Proof.** Relabeling applies $f$ to the variables in each literal of each clause, without changing the number of literals in any clause or the number and order of clauses. Consequently every clause keeps the same weight, its length plus one, and summing these unchanged weights shows that the cost is preserved.
