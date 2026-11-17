<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.dgSpan_generate_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Leftward Sweep Span

**Claim.** Under the stated transition rule, the machine’s first $n$ steps write the first $n$ symbols of $w$ while sweeping left, reach the specified configuration with frontier $z-n$, and keep the work head in $[z-n,z]$.

**Proof.** For each prefix length $u\le |w|$, apply the sweep-generation result with displacement $-1$. The one-step hypothesis, together with the fact that a leftward sweep action applied to a backward-sweep configuration advances the state, decreases the frontier by one, prepends the newly written symbol to the left zipper, and removes the first entry of the right zipper (`Turing.FinTM.sweepRevCfg_left_any`), verifies its step condition. The sweep-generation formula then gives the configuration after $n$ steps: its frontier is $z+(-1)n=z-n$, its left zipper is the reversed list of the first $n$ symbols, and its right zipper has dropped those $n$ entries. For every intermediate time $u\le n$, the same formula gives head position $z-u$. Since $0\le u\le n$, this lies between $z-n$ and $z$, proving the span bound.

**Key facts.** `Turing.FinTM.sweepRevCfg_left_any`, `Turing.FinTM.sweep_generate`.
