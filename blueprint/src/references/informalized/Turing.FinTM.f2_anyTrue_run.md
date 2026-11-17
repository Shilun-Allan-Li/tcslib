<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_anyTrue_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Any-True Machine Run

**Claim.** For a split $x=pr$, there is a time at most $|r|+1$ when the any-true machine, started scanning just after $p$ with empty output, is halted and has output consisting of the single bit indicating whether $r$ contains a true bit.

**Proof.** Induct on $r$. If it is empty, the machine sees the end of the input and halts in one step, emitting the false bit, which is the any-true value of the empty word. If $r=b::s$ and $b$ is true, the machine halts immediately and emits true, as required. If $b$ is false, its scanning transition moves right, emits nothing, and remains in the scanning state; this is the scan-step fact `f2_scanStep_right`. The induction hypothesis applies to the remaining suffix from prefix $p++[false]$. Prepending that transition gives a halting run with the same output, since a false leading bit does not change whether the suffix contains a true bit. The run equation `runFrom_succ_eq_step` and the length relation give the asserted bound. The reading fact `f2_scanCfg_read` identifies the first symbol, and the zero- and one-step run equations (`runFrom_zero`, `runFrom_succ_eq_step`) handle the immediate halting cases.

**Key facts.** `Turing.FinTM.f2_scanCfg_read`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.FinTM.f2_scanStep_right`.
