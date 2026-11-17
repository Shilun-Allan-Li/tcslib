<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/FormulaKit/Gate.lean :: Complexity.FormulaKit.cost_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cost of Concatenated Formulas

**Claim.** For any two conjunctive normal forms $\varphi$ and $\psi$ over the same variable type, the cost of their concatenation is the sum of their costs.

**Proof.** The cost assigns each clause $C$ the weight $|C|+1$ and sums these weights over the formula's list of clauses. Concatenating the two clause lists preserves their order and places the clauses of $\psi$ after those of $\varphi$. The sum over this concatenated list is the sum over the first list plus the sum over the second, giving $\operatorname{cost}(\varphi++\psi)=\operatorname{cost}(\varphi)+\operatorname{cost}(\psi)$.
