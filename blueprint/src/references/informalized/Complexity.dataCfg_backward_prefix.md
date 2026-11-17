<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean :: Complexity.dataCfg_backward_prefix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Backward Sweep Prefix Invariant

**Claim.** Under the stated guide, current-payload, and cached-neighbor hypotheses, after $n\le 2R+1$ backward-phase steps the guide head is at $R-n$, the registers contain the prescribed payloads, and the resulting tape contents satisfy the stated current-payload and cached-neighbor invariants.

**Proof.** Proceed by induction on $n$. At $n=0$, take the tape contents unchanged. The run has made no steps, and the two payload assertions reduce directly to the assumed current-payload and cached-neighbor identities; the conditional current-payload formula selects the unchanged value because no coordinate lies strictly above $R$ and at most $R$.

For the successor step, write $g=R-n$ and take tape contents $T'$ from the induction hypothesis. At coordinate $g$, the induction invariant says the current payload is $f(g)$. The cached left-neighbor payload there is $f(g-1)$, since $g$ is within the original guide interval and the induction hypothesis preserves that cached-neighbor invariant. The carried register from the preceding position is $f(g+1)$. Thus, according to whether the virtual movement is left, stationary, or right, the backward-step update selects respectively $f(g-1)$, $f(g)$, or $f(g+1)$, which is exactly $f(g+m_i)$ for movement $m_i$.

Apply the one-step backward-phase description (`dataCfg_backward_step`) after rewriting the run of $n+1$ steps as one step after the run of $n$ (`runFrom_succ_eq_step'`). It moves the guide head from $g$ to $g-1$, carries the current payloads at $g$ into the registers, and updates precisely coordinate $g$, storing the selected payload there with a blank cached neighbor. This makes the new current-payload formula hold at $g$, which is now in the updated interval; at every other coordinate the tape is unchanged and the interval condition agrees with the induction formula. For the cached-neighbor assertion, any coordinate in the new required range differs from $g$, so its tape cell is unchanged and the induction hypothesis applies. This proves all three conclusions at $n+1$.

**Key facts.** `Turing.MultiTapeTM.runFrom_zero`, `Complexity.dataCfg_backward_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
