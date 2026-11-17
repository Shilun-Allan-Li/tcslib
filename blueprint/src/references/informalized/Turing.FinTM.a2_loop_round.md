<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.a2_loop_round -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A loop round with bounded heads

**Claim.** Under the stated body-run, space, and fuel-head hypotheses, the loop host either halts or completes a successful debit and returns to the ready configuration for the next seam, while all heads stay within radius $B+2|word|+6$.

**Proof.** Let $start$ be the body seam configuration with state $anchor$ and word $s$. It is live, and all its work heads are at zero. Split on whether $accepted$ is true.

If it is true, take the first halting time $u$ of the body run. The first-halt lemma gives $u>0$, live configurations before $u$, and equality between the configuration at $u$ and the stated terminal configuration. The host's halt-return property shows that it reaches a call on this halted body configuration with its success flag set. The host's accept procedure then halts after a bounded number of steps; since the body's output is $[true]$, this extra phase lasts at most five steps. The head estimate for the host's call prefix is supplied by `a2_call_prefix`; the remaining short phase is bounded by the per-step displacement estimate (`a2_heads_steps`), and `a2_heads_join` combines the two intervals. The resulting host configuration is halted.

If $accepted$ is false, the terminal body configuration is the next seam. The run stays live through time $t$ (`f2_loop_live_prefix`), so `a2_call_prefix` bounds the host heads up to that time. The host's anchor-return property takes one further step and produces a call on the next seam with a false flag and the payload initialized for the debit procedure. The reject procedure (`f2_loopHost_reject`) either finishes the debit and restores the ready configuration with the debited payload, or halts when no true bit can be debited. Its duration is at most $2|word|+4$; the head-displacement bound extends the prefix radius to $B+2|word|+6$, and `a2_heads_join` combines the prefix and this final phase. Splitting on whether the debit succeeds yields exactly the two alternatives in the claim. Run concatenation in both cases uses the fact that a run of $a+b$ steps is a run of $a$ steps followed by $b$ (`runFrom_add`).

**Key facts.** `Turing.FinTM.f2_loop_first_halt`, `Turing.FinTM.f2_loopHost_halt_return`, `Turing.FinTM.f2_loopHost_accept`, `Turing.FinTM.a2_call_prefix`, `Turing.FinTM.a2_heads_steps`, `Turing.FinTM.a2_heads_join`, `Turing.FinTM.f2_loop_live_prefix`, `Turing.FinTM.f2_loopHost_anchor_return`, `Turing.FinTM.f2_loopHost_reject`, `Turing.MultiTapeTM.runFrom_add`.
