<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean :: Turing.ClockHost.slots_sI -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Assignment on the first tape block

**Claim.** At the combined index corresponding to any index $i$ in the first block, the assembled function has value $f(i)$.

**Proof.** The combined index $sI(i)$ is obtained by placing $i$ in the first block and extending it past the second block and the final singleton. By the defining behavior of the appended function on its first block, evaluating the assembled function there returns $f(i).
