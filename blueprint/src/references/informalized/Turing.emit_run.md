<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Wrappers.lean :: Turing.emit_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Forwarding a Run

**Claim.** If the host transitions at forwarded states agree with the forwarding transform of the source transitions, and the source run is not halted before time $t$, then the host run from the forwarded initial configuration agrees after $t$ steps with the forwarded source run.

**Proof.** First consider one step from a nonhalted source configuration. Its state must be some state $s$. The forwarded configuration has state $\iota(s)$, scans the same input symbol, and has the same scanned work-tape symbols. The transition agreement and the fact that forwarding commutes with applying an action (`Turing.emit_apply`) show that the host's next configuration is the forwarded image of the source's next configuration. Now induct on $t$. The zero-step claim is immediate. For the successor case, the run-recurrence formula expresses each run at time $t+1$ as one step from its time-$t$ configuration (`Turing.MultiTapeTM.runFrom_succ_eq_step'`). The source configuration at time $t$ is nonhalted by the hypothesis, so the one-step result applies there; the induction hypothesis identifies the configurations at time $t$. Combining these gives the required equality at time $t+1$.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.emit_apply`.
