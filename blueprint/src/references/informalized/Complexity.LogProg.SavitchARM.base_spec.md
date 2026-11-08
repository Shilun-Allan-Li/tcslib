<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Recursion.lean :: Complexity.LogProg.SavitchARM.base_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Base-Level Reachability Simulation

**Claim.** Under the level-zero invariant and $s\le w$, the program reaches the appropriate return label in finitely many steps, with the returned Boolean equal to level-zero reachability and with every earlier configuration safe and bounded.

**Proof.** First, the invariant’s register bounds imply that the starting registers are bounded by $2^{w^2}$ (`Complexity.LogProg.SavitchARM.Inv.bd`), which supplies the safety bound needed to prepend program steps. From label $\mathrm{cl}$ at level zero, the program takes one step to the base check and then queries the step oracle with the encoding of $x$, the source code, the target code, and $s$. The virtual-input encoding for this three-register query is exactly the nested pair encoding (`Complexity.LogProg.vword_whole₃`). If the oracle relation holds, level-zero reachability holds by its edge clause, so the program returns true. If the oracle relation fails, it checks whether source and target codes are equal: equality gives reachability by the identity clause; inequality rules out both clauses in the level-zero definition, so the program returns false. In each case the remaining execution is immediate, and reflexive reachability lets us close it with no further steps (`Complexity.LogProg.AReach.refl`). The bounded-step principle (`Complexity.LogProg.SavitchARM.step_of`) prepends the initial transitions while retaining the safety bound.

**Key facts.** `Complexity.LogProg.SavitchARM.Inv.bd`, `Complexity.LogProg.SavitchARM.step_of`, `Complexity.LogProg.vword_whole₃`, `Complexity.LogProg.AReach.refl`.
