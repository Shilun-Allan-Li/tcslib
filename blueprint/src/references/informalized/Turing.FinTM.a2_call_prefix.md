<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.a2_call_prefix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Head Bounds During a Captured Loop Prefix

**Claim.** Under the stated live-run, anchor, space, and output-length hypotheses, every work-tape head of the loop host run through time $t$ lies in $[-B,B]$.

**Proof.** Fix $u\le t$. The simulation lemma `a2_call_run` identifies the host configuration at time $u$ with a captured call whose body configuration is the body's run at time $u$; its release value is retained only at time zero, and its additional flag records whether the body has halted. The hypotheses for that simulation hold because every time before $t$ is also before or equal to the chosen prefix bound, and the live and anchor conditions are assumed for all times strictly less than $t$. Each original body head at time $u$ lies in $[-B,B]$ by `a2_source_radius`: the heads began at zero and the body uses at most $B$ cells through time $u$. The fuel heads satisfy the given bound. Finally, the body's output at time $u$ has length at most $B$: its output is a prefix of the output at time $t$ (`output_prefix`), whose length is bounded by hypothesis. Applying the captured-call head bound (`a2_call_heads`) gives the desired bound at time $u$. Since $u$ was arbitrary, it holds throughout the prefix.

**Key facts.** `Turing.FinTM.a2_call_run`, `Turing.FinTM.a2_source_radius`, `Turing.MultiTapeTM.output_prefix`, `Turing.FinTM.a2_call_heads`.
