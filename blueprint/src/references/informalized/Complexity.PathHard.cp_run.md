<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardMachine.lean :: Complexity.PathHard.cp_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copy-Site Execution

**Claim.** If every register is bounded by $B$ and the destination value is no greater than the source value, the machine reaches the next label with the destination replaced by the source value, all other registers unchanged, and the guard maintained throughout.

**Proof.** At a copy site, the machine first compares the destination and source registers. If they are equal, it proceeds directly to the next label. Otherwise it repeatedly increments the destination and returns to the comparison, until it equals the source. The destination starts no larger than the source, so these increments terminate at the source value and never exceed $B$. The source is distinct from the destination (`Complexity.PathHard.cp_ne`), so it remains fixed during the loop. The guarded copy-loop result (`Complexity.LogProg.registerCopy_loop`) packages this argument: given the register bounds, the initial inequality, the inequality of the two register indices, and the specified compare/increment transitions, it yields reachability of the next label with exactly the destination updated and the guard true throughout. The componentwise register bound needed there follows from the record bound (`Complexity.PathHard.St.Bd.toV`).

**Key facts.** `Complexity.PathHard.cp_ne`, `Complexity.LogProg.registerCopy_loop`, `Complexity.PathHard.St.Bd.toV`.
