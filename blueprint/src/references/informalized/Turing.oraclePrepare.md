<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oraclePrepare -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oracle Preparation from a Bookmark

**Claim.** From the bookmark configuration, the dispatch machine reaches the ready configuration with empty argument and copy state within $|p|+3$ steps, and every earlier state is a bookmark, origin, or save state.

**Proof.** Separate the case $p=0$. The preparation-at-zero calculation (`Turing.oraclePrepare_zero`) reaches the desired configuration in two steps, within the bound. The only earlier times are $0$ and $1$: the first is the bookmark state and the second is the save state.

For $p\ne0$, the side condition gives the signed-distance identity $p=d|p|$, where $d=1$ on the true side and $d=-1$ on the false side (`Turing.oracleSide_distance`). The origin walk therefore reaches position $0$ after $|p|$ steps (`Turing.oracleOrigin_run`). The initial bookmark transition marks the origin and enters the origin state (`Turing.oracleMark_step`); the two-step preparation tail from position $0$ then reaches the ready configuration (`Turing.oraclePrepare_tail`). Together these take $|p|+3$ steps. Before the endpoint, time zero is the bookmark state; the subsequent walk steps are in the origin state; and the final step before completion is in the save state. These cases give the asserted state classification.

**Key facts.** `Turing.oraclePrepare_zero`, `Turing.oracleSide_distance`, `Turing.oracleOrigin_run`, `Turing.oracleMark_step`, `Turing.oraclePrepare_tail`.
