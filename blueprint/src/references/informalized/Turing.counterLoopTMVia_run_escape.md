<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.counterLoopTMVia_run_escape -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counter Loop Run to Escape

**Claim.** If the rounds through $r_0$ satisfy the stated conditions and the next configuration is in state $e$, then at the stated time the counter-loop machine is in its escape configuration with the counter word after $r_0+1$ decrements on the extra tape. Before then it is neither done nor escape; throughout the interval the extra head stays within the stated bounds and the first $k$ head positions track the specified runs.

**Proof.** Substitute the given expression for $T$. Apply `Turing.counter_rounds` for $r_0+1$ rounds. The hypotheses ensure its intermediate-state condition: being outside the round’s exit set $\{some\ e\}$ means a live intermediate state is not $e$, while the round condition already excludes $a$. The resulting execution theorem gives the endpoint tape patch, the span and tracking assertions, and the pre-endpoint exclusions. At the endpoint, redirecting the body’s state sends $e$ to escape: the state is not $a$ because $e\ne a$, and it is the designated exit. The counter word has the same length as the original word by `Turing.counterWord_length`, so the patched tape has exactly the stated buffer domain. The theorem’s tracking index bound is converted from a strict inequality to $r\le r_0$ by the elementary equivalence $r<r_0+1\iff r\le r_0$.

**Key facts.** `Turing.counterWord_length`, `Turing.counter_rounds`.
