<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.macroCfg_seek_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix of the leftward seek

**Claim.** If $n\le R+1$, then after $n$ steps from the leftward-seek phase with guide head at $0$, the machine remains in that phase and its guide head is at $-n$.

**Proof.** Induct on $n$. At zero steps this is the starting configuration. For the successor step, the induction hypothesis puts the guide head at $-n$. From $n<R+1$ we get $n<R+1$, so $-n$ is strictly greater than the left-edge coordinate $-R-1$; the head has not reached that edge. The one-step seek rule (`macroCfg_seek`) therefore keeps the machine in the seek phase and moves the head left to $-(n+1)$. The run successor rule supplies the iteration step (`runFrom_succ_eq_step'`).

**Key facts.** `Complexity.macroCfg_seek`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
