<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenWalk.lean :: Complexity.LogProg.ISGen.gwalk_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Walk Initialization Correctness

**Claim.** The walk initialization state has semantics that the target belongs to the bounded reachable set and that the continuation property $Q$ holds.

**Proof.** The initialization instruction clears the guess register and then enumerates candidate initial codes $j<K$. For each candidate, the initial-code oracle determines whether it is a valid start. If it is, the program copies $j$ into the current-code register and enters the walk loop with step count zero. The walk-loop correctness theorem (`gwalk_loop`) then says that this branch has semantics consisting of a walk from $j$ to the target within the remaining step bound, together with $Q$; the hypothesis on $Q$ supplies the continuation semantics once such a walk is established. If the initial-code oracle rejects $j$, that branch rejects and contributes no accepting run. The guess-loop theorem (`nsem_guess`) combines these branches: its existential witness is exactly a code $j$ with $j<K$, valid initial status, the required walk, and $Q$. By the definition of `Mem`, this existential statement is equivalent to `Mem` and $Q$ together. Finally, the outer clearing instruction preserves the semantics while resetting the guess register, and the register bounds ensure the configurations used in these steps satisfy the program's guard.

**Key facts.** `Complexity.LogProg.ISGen.St.greg`, `Complexity.LogProg.NSem.clr`, `Complexity.LogProg.nsem_guess`, `Complexity.LogProg.ISCount.St.toV_K`, `Complexity.LogProg.ISGen.gwalk_loop`, `Complexity.LogProg.ISGen.IG.of_eq`.
