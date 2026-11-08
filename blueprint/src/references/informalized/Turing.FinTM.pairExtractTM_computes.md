<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.pairExtractTM_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair component extraction time bound

**Claim.** For any flags $f_1,f_2$ and finite bit string $x$, the extractor halts within $5(|x|+1)$ steps with the selected components of the decoded pair concatenated in order, or with the empty string if decoding fails.

**Proof.** The run lemma `extract_run` supplies a halting time $t\le 3|x|+2|x|+5=5(|x|+1)$, together with the required output, starting from the machine's initial configuration. The initial configuration is exactly the specialized extraction configuration with empty prefix and empty stored component; this follows by comparing their state, input position, work tape, and output. The characterization of computation in time (`computesInTime_iff`) then turns the halting state and output established by the run lemma into the machine's computation claim at time $t$. Finally, monotonicity of computation time (`ComputesInTime.mono`) extends this to the stated bound.

**Key facts.** `Turing.FinTM.extract_run`, `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.mono`.
