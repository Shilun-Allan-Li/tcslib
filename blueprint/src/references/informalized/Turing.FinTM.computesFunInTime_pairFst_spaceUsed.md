<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.computesFunInTime_pairFst_spaceUsed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First-component extraction with linear space

**Claim.** A finite Boolean Turing machine extracts the first parsed component, or outputs the empty word if parsing fails, within $6(|x|+1)$ steps and uses at most $6(|x|+1)$ work-tape cells at every time.

**Proof.** Choose the first-component extraction machine. Its computation takes $5(|x|+1)$ steps and has the claimed output on successful and failed parses (`f2_pairExtract_computes`); the computation bound can be increased to $6(|x|+1)$ without changing that output (`ComputesInTime.mono`). The general time-to-space estimate bounds space at every time by the number of work tapes times the time bound plus one (`f2_space_of_time`). This machine has one work tape, so the estimate is $5(|x|+1)+1$, which is at most $6(|x|+1)$.

**Key facts.** `Turing.FinTM.f2_pairExtract_computes`, `Turing.FinTM.ComputesInTime.mono`, `Turing.FinTM.f2_space_of_time`.
