<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Recursion.lean :: Complexity.LogProg.SavitchARM.loop_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Midpoint search loop specification

**Claim.** Under the recursive-call property at level $i$, the loop scans the candidate midpoints from the current $M$ up to the bound and returns with an answer that is true exactly when some candidate midpoint witnesses both level-$i$ reachability relations.

**Proof.** Proceed by induction on the number $k$ of remaining candidates, using $M+k=2^w$. When $k=0$, the invariant gives $M=2^w$, so the loop exits immediately with false; no admissible midpoint remains, and reflexivity of machine reachability supplies the run for this single step. For the successor case, $M<2^w$. First use the descent results to test the two level-$i$ relations through the current midpoint: `desc1` tests reachability from $U$ to $M$, and `desc2` tests reachability from $M$ to $V$. If both hold, the midpoint itself witnesses the desired existential, and `tail1T` completes the successful return. If the first test fails, or if the first succeeds and the second fails, the current midpoint cannot witness the conjunction. The loop advances to $M+1$ by `tail0F` or `tail1F`, respectively, and the induction hypothesis handles the remaining $k$ candidates. In each failure case, `exists_shift` shows that the existential over candidates beginning at $M$ is equivalent to the existential beginning at $M+1$, since the conjunction fails at $M$. Concatenating these finite runs with `AReach.trans` yields the required run. The invariant bound ensures the guard throughout, and `Inv.setM` preserves the invariant when the midpoint advances.

**Key facts.** `Complexity.LogProg.SavitchARM.Inv.bd`, `Complexity.LogProg.SavitchARM.Inv.setM`, `Complexity.LogProg.AReach.refl`, `Complexity.LogProg.SavitchARM.desc1`, `Complexity.LogProg.SavitchARM.desc2`, `Complexity.LogProg.SavitchARM.tail1T`, `Complexity.LogProg.SavitchARM.exists_shift`, `Complexity.LogProg.SavitchARM.tail0F`, `Complexity.LogProg.SavitchARM.tail1F`, `Complexity.LogProg.AReach.trans`, `Complexity.LogProg.SavitchARM.step_of`.
