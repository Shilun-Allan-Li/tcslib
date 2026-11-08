<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.macroCfg_check -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counter Test Step

**Claim.** From the counter-test phase, one schedule step enters the leftward-seek phase exactly when the base unary-counter tape has a unit marker at position $u$; otherwise the controller halts, while the unary-counter and guide heads remain at $u$ and $g$.

**Proof.** The counter-test transition checks the unary-counter symbol at the current head position. By `Complexity.macroCfg_unary`, this is the base unary-counter tape symbol at $u$. If it is the unit marker, the transition enters the leftward-seek phase; otherwise it has no successor state and the controller halts. In either branch the transition leaves both added-tape head movements at zero. The resulting state and unchanged head positions give the stated macro configuration by `Complexity.macroCfg_apply`.

**Key facts.** `Complexity.macroCfg_unary`, `Complexity.macroCfg_apply`.
