<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordRun_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of the Recorded Run Radius

**Claim.** If a run satisfies the recorded-run conditions with radius $r$, then for every $r'\ge r$ it satisfies those same conditions with radius $r'$.

**Proof.** The endpoint equality and the avoidance of the distinguished states are unchanged. For every time through $t$ and every work tape, the original bound gives a distance at most $r$. Since $r\le r'$, the same distance is at most $r'$, so all recorded-run conditions hold with the larger radius.
