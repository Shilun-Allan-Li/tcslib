<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_pairExtract_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair Extraction Computation

**Claim.** For every finite bit string $x$ and Boolean flags $a,b$, the constructed machine outputs the first parsed component when $a$ is true, followed by the second parsed component when $b$ is true, omitting unselected components and outputting nothing if parsing fails, within $5(|x|+1)$ steps.

**Proof.** Apply the extraction-run lemma to the whole input, with empty prefix and empty already-collected first component. It gives a halting run with exactly the specified output, in some time $t$ bounded by $3|x|+2\cdot 0+5=3|x|+5$, hence by $5(|x|+1)$ (`Turing.FinTM.f2_extract_run`). The initial configuration of the constructed machine is the extraction lemma's starting configuration with these choices. The computation characterization converts the lemma's halting and output facts into a computation claim (`Turing.FinTM.computesInTime_iff`); monotonicity then raises the time bound to $5(|x|+1)$ (`Turing.FinTM.ComputesInTime.mono`).

**Key facts.** `Turing.FinTM.f2_extract_run`, `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.mono`.
