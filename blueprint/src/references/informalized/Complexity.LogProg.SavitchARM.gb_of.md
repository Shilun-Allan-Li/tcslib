<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Run.lean :: Complexity.LogProg.SavitchARM.gb_of -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Bounds Give the Guard

**Claim.** If all eighteen registers of a state are at most $B$, then for every program label the corresponding configuration with no answer satisfies the guard: its registers are bounded by $B$ and its instruction meets the guard precondition.

**Proof.** The guard has two requirements. The machine's precondition lemma says that every configuration of this program satisfies the instruction precondition (`Complexity.LogProg.SavitchARM.preS_A`). The state bound gives a bound by $B$ for every coordinate of its register vector (`Complexity.LogProg.SavitchARM.St.Bd.toV`). Combining these facts proves both parts of the guard.

**Key facts.** `Complexity.LogProg.SavitchARM.preS_A`, `Complexity.LogProg.SavitchARM.St.Bd.toV`.
