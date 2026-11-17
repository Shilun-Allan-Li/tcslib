<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/DNF.lean :: Std.Sat.CNF.tautology_dual_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dual tautology and unsatisfiability

**Claim.** A CNF formula over variables indexed by $\mathbb{N}$ has a tautological DNF dual exactly when the CNF is unsatisfiable.

**Proof.** Fix any Boolean assignment $a$. The dual evaluation identity says that the DNF dual evaluates to the negation of the CNF evaluation ($\mathrm{eval\_dual}$). Thus the dual is true for every assignment exactly when the CNF evaluates to false for every assignment. The latter is precisely the negation of the existence of an assignment satisfying the CNF.

**Key facts.** `Std.Sat.CNF.eval_dual`.
