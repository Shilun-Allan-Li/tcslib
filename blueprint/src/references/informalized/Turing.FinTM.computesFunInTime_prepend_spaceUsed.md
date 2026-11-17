<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.computesFunInTime_prepend_spaceUsed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear-Time Prefixing with Bounded Space

**Claim.** For every Boolean word $w$, there are a finite Turing machine and a natural number $c$ such that on input $x$ the machine outputs $wx$ within $c(|x|+1)$ steps and uses at most $c$ work-tape cells at every time.

**Proof.** Take the catalog prefix machine. It computes $wx$ in $|w|+|x|+1$ steps; with $c=|w|+1$, this is at most $c(|x|+1)$. The machine has zero work tapes, so its total work space is zero at every time, which is at most $c$.

**Key facts.** `Turing.FinTM.f2_catalogPrefixTM_computes`, `Turing.MultiTapeTM.spaceUsed_zero_tapes_eq_zero`, `Turing.FinTM.ComputesInTime.mono`.
