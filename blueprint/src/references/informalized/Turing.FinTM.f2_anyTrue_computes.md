<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_anyTrue_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Any-True Boolean Computation

**Claim.** The designated finite Turing machine computes the function sending each Boolean word $x$ to the one-symbol word whose bit is true exactly when some bit of $x$ is true, in time $|x|+1$.

**Proof.** Fix an input $x$. The run lemma for the any-true machine (`f2_anyTrue_run`), applied to the whole input suffix, provides a halting run with output $[x.any\ id]$ in at most $|x|+1$ steps. The machine's initial configuration is the scanning configuration at position zero with empty output; equality of these configurations follows by extensionality on their state, input position, and output (`Cfg.ext_zero_tapes`). The characterization of computation in time (`computesInTime_iff`) turns the run's state and output conclusions into the computation claim at that time. Finally, time monotonicity (`ComputesInTime.mono`) extends the bound to exactly $|x|+1$ steps.

**Key facts.** `Turing.FinTM.f2_anyTrue_run`, `Turing.Cfg.ext_zero_tapes`, `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.mono`.
