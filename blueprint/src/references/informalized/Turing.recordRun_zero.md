<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordRun_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-Length Recorded Run

**Claim.** A configuration satisfying the head-position bound forms a recorded run to itself in zero steps, with the required state avoidance and head bounds.

**Proof.** At time zero the run is the initial configuration itself, so its endpoint is $a$. There are no natural numbers strictly below zero, making the state-avoidance condition vacuous. If $u\le 0$, then $u=0$, and the head-position condition is exactly the assumed bound for $a$.
