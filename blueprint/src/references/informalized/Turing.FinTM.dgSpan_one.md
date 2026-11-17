<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.dgSpan_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Span Bound

**Claim.** If one machine step takes $c$ to $d$ and both endpoint head positions lie in $[\mathrm{lo},\mathrm{hi}]$, then the one-step run reaches $d$ and stays within those bounds at times zero and one.

**Proof.** A run of one step is the machine’s single-step transition, so the assumed equation identifies its endpoint with $d$. The only natural times $u\le1$ are $0$ and $1$. At time zero the configuration is $c$, whose head position satisfies the bounds by hypothesis; at time one it is $d$, whose head position also satisfies them by hypothesis.
