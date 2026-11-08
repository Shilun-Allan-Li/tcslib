<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_rawStrip_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Raw strip running time

**Claim.** For every Boolean word $x$, the raw strip machine outputs the prefix strictly before the last true in $x$, or the empty word if there is no true, within $4(|x|+1)$ steps.

**Proof.** The copying lemma (`f2_rawStrip_copy`) says that after $|x|$ steps the machine has copied all of $x$ to its work tape. One more step moves it into the trimming state at the end of that copy; the resulting configuration is identified directly with the stated trimming-start configuration. Apply the trimming bound (`f2_rawStrip_trim`) to the copied word $x$, obtaining a further $t\le3(|x|+1)$ steps to halt with output $(\mathrm{splitAtLastTrue}(x)).\mathrm{getD}([])$. The run concatenation law (`runFrom_add`) combines the copy and trim segments. The computation characterization (`computesInTime_iff`) turns the halted state and output into computation at time $|x|+1+t$, and monotonicity (`ComputesInTime.mono`) raises this to $4(|x|+1)$, since $|x|+1+t\le4(|x|+1)$.

**Key facts.** `Turing.FinTM.f2_rawStrip_copy`, `Turing.FinTM.f2_rawStrip_trim`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.mono`.
