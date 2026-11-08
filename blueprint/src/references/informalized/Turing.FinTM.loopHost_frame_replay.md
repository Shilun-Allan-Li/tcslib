<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopHost_frame_replay -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Replay of a Stored Word

**Claim.** From phase $13$ with payload word $w$, payload head at zero, and empty output, after $|w|+1$ steps the host is halted and has output exactly $w$.

**Proof.** Express the given configuration as the replay configuration used by the replay lemma, with the other tape contents and head positions carried as parameters. The replay lemma scans the payload, appending its symbols to the output, and after one additional step reaches a halted configuration whose output is the initial output followed by $w$. Here the initial output is empty, so the resulting output is exactly $w$, and the state is halted.

**Key facts.** `Turing.FinTM.loopHost_replay`.
