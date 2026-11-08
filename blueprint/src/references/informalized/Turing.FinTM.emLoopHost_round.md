<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emLoopHost_round -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Emitting Loop Round

**Claim.** Under the stated body-run and anchor-avoidance hypotheses, the forwarding loop host reaches the next seam configuration with one decrement of the counter, or halts on underflow, within the stated time bound and with output chunk.

**Proof.** Let $c$ be the starting seam configuration. The anchor-avoidance hypothesis, together with the fact that the call begins released, supplies the intermediate-state condition needed to apply the loop host's anchor-return theorem (`loopHost_anchor_return`). That theorem shows that after $t+1$ host steps the computation has returned from the body run to the host in its post-round configuration, with the body output chunk recorded. The initial forwarding call with empty prefix is the ordinary call because $c$ has empty output (`emLoopCall_empty`); the forwarding-call decomposition (`emLoopCall_frame`) then identifies the returned host configuration with the ordinary loop call on the halting body configuration and with output chunk. Apply the host's rejection/decrement analysis (`loopHost_reject`) to this halting configuration: within at most $2|w|+4$ further steps, the counter either decrements successfully and the host reaches the next released seam call, or underflows and halts. The total is at most $(t+1)+(2|w|+4)=t+2|w|+5$. The output-prefix preservation law for runs (`runFrom_output_prepend`) ensures that the chunk already produced during the body run remains the output through the administrative continuation; concatenating with the empty output of the administrative configuration leaves exactly the chunk. Combining the two run segments uses the run-addition law (`runFrom_add`).

**Key facts.** `Turing.FinTM.loopHost_anchor_return`, `Turing.FinTM.emLoopCall_empty`, `Turing.FinTM.emLoopCall_frame`, `Turing.FinTM.loopHost_reject`, `Turing.MultiTapeTM.runFrom_output_prepend`, `Turing.MultiTapeTM.runFrom_add`.
