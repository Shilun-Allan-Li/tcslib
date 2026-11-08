<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/CNF.lean :: Complexity.eval_congr_of_lt_numVars -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation from occurring variables

**Claim.** If two Boolean assignments agree on every variable below the variable count of a CNF formula, then the formula has the same evaluation under both assignments.

**Proof.** The CNF evaluation congruence principle says that two assignments give the same formula value whenever they agree on every variable occurring in the formula (`Std.Sat.CNF.eval_congr`). It remains to check that each occurring variable lies below the stated bound. An occurrence of $v$ appears as the index of a literal, either $(v,\mathrm{false})$ or $(v,\mathrm{true})$. Thus $v+1$ occurs in the list whose fold by maximum defines $N(\varphi)$. Every member of a list is at most its fold by maximum (`le_foldr_max_of_mem`), so $v+1\le N(\varphi)$ and hence $v<N(\varphi)$. The assumed agreement therefore applies to each occurring variable, and the congruence principle gives the result.

**Key facts.** `Complexity.le_foldr_max_of_mem`.
