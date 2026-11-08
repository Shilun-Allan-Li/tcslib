<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.accessPath_of_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Safe Runs Define Access Paths

**Claim.** If every configuration before time $T$ in an access-program run has all work-head positions within the specified bounds, then the run from its initial configuration to time $T$ is an access path.

**Proof.** Induct on $T$. At time zero, the run has length zero, so it is an access path by reflexivity. For the successor case, the run to time $T+1$ consists of the run to time $T$ followed by one program step (`Complexity.LogProg.rrun_succ`). The induction hypothesis applies because every time strictly before $T$ is also strictly before $T+1$. The additional step is permitted because the configuration at time $T$ satisfies the assumed head-position bound. Appending that permitted step gives the desired access path.

**Key facts.** `Complexity.LogProg.rrun_succ`.
