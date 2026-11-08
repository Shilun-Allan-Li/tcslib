<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.taut_eval_congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# DNF Evaluation Depends on Bounded Variables

**Claim.** If two assignments agree at every index below the variable count of a DNF's terms, then the DNF evaluates identically under both assignments.

**Proof.** View the DNF as the dual of a CNF. The dual-dual identity (`Std.Sat.DNF.dual_dual`) recovers the original DNF, and evaluating a dual CNF negates the original evaluation (`Std.Sat.CNF.eval_dual`). The variable count of this dual CNF is exactly the stated count for the DNF terms (`Complexity.taut_numVars_dual`), so the two assignments agree below the dual's variable count. CNF evaluation depends only on variables below its variable count (`Complexity.eval_congr_of_lt_numVars`); hence the dual CNF has equal evaluations under the assignments. Negating these equal values, and identifying the double dual with the original DNF, gives the desired equality.

**Key facts.** `Complexity.taut_numVars_dual`, `Complexity.eval_congr_of_lt_numVars`, `Std.Sat.DNF.dual_dual`, `Std.Sat.CNF.eval_dual`.
