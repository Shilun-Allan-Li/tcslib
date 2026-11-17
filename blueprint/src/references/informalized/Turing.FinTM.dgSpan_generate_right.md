<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.dgSpan_generate_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rightward Sweep Span

**Claim.** Under the stated transition rule, the machine’s first $n$ steps write the first $n$ symbols of $w$ while sweeping right, reach the specified configuration with frontier $z+n$, and keep the work head in $[z,z+n]$.

**Proof.** For each prefix length $u\le |w|$, use the sweep-generation result with displacement $1$. The transition hypothesis and the effect of a rightward sweep action on a forward-sweep configuration (`Turing.FinTM.sweepCfg_right_any`) give exactly its one-step update: the state advances, the frontier increases by one, the written symbol is prepended to the left zipper, and the right zipper loses its first entry. Thus after $n$ steps the frontier is $z+1\cdot n=z+n$, and the zipper lists have the asserted forms (`Turing.FinTM.sweep_generate`). At each intermediate time $u\le n$, this formula also gives head position $z+u$, which lies in $[z,z+n]$.

**Key facts.** `Turing.FinTM.sweepCfg_right_any`, `Turing.FinTM.sweep_generate`.
