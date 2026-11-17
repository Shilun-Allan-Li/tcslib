<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.a2_source_radius -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space bounds the work head radius

**Claim.** If every work head starts at $0$ and total visited work space through time $t$ is at most $B$, then each work head at time $t$ lies in $[-B,B]$.

**Proof.** Fix a tape and argue that all integer positions between $0$ and its head position at time $u$ have been visited by time $u$. At time zero this holds because the head is at $0`. At each step, the head moves by at most one cell (`workTapePos_step_le`), so the interval between $0$ and its new position either lies in the previous interval or adds only the new endpoint. The run-step relation `runFrom_succ_eq_step'` identifies that new position as the head after one transition; the initial case uses `runFrom_zero`. Thus the interval from $0$ to the head at time $t$ is contained in the visited set. Its cardinality is at least the absolute value of the head position plus one, while the visited-set size for this tape is no greater than total space (`spaceUsedByTape_le_spaceUsed`). Since total space is at most $B$, the head’s absolute value is at most $B$, which is the claimed pair of bounds.

**Key facts.** `Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.workTapePos_step_le`, `Turing.MultiTapeTM.spaceUsedByTape_le_spaceUsed`.
