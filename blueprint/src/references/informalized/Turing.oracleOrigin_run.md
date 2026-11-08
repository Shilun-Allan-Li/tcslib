<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleOrigin_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oracle Origin Walk

**Claim.** Starting from the marked configuration, for each $u\le |p|$ the dispatch machine is in the corresponding origin-walk configuration, with the first two heads displaced from $p$ by the prescribed unit steps.

**Proof.** For every $u<|p|$, the walk position $p+du$, where $d=-1$ on the true side and $d=1$ on the false side, is nonzero. Indeed, the side hypothesis fixes the sign of $p$, and before $|p|$ unit moves the walk has not yet reached the origin. At such a position the tape-1 bookmark marker, originally placed at $p$, is not the true origin marker at cell $0$ (`Turing.oracleBookmark_ne_origin`). Consequently the origin-state transition continues the unit walk, moving both leading heads by $d$ and changing no other configuration data.

The repeated-walk result (`Turing.oracleWalk_run`) now applies for the full $|p|$ steps, since its transition condition holds at every earlier walk position. The marked configuration agrees with the walk configuration at position $p$ (`hstart` in the proof), so the resulting formula holds for every $u\le |p|$, including the endpoint.

**Key facts.** `Turing.oracleBookmark_ne_origin`, `Turing.oracleWalk_run`.
