<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.dgSpan_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concatenating Bounded Computation Spans

**Claim.** If a computation from $c$ to $d$ and then a computation from $d$ to $e$ both keep the work head in $[\mathrm{lo},\mathrm{hi}]$, their concatenation reaches $e$ in the sum of the two durations and stays in that interval throughout.

**Proof.** The run-composition identity says that running for $s+t$ steps is the same as running for $s$ steps and then for $t$ more steps (`Turing.MultiTapeTM.runFrom_add`). Applying it to the first endpoint and then the second shows that the combined run ends at $e$. For any time $u\le s+t$, split into two cases. If $u\le s$, the first span already gives the required bounds. Otherwise write $u=s+(u-s)$; then $u-s\le t$, and run composition identifies the configuration at time $u$ with the configuration reached after $u-s$ steps from $d$. The second span supplies both bounds there.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`.
