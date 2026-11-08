<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.FinOracleNDTM.choiceOut_eq_true_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of a true choice output

**Claim.** The choice output is exactly $[\mathrm{true}]$ if and only if the run halts and its output is exactly $[\mathrm{true}]$.

**Proof.** Let $c$ be the configuration reached by the specified run. If $c$ is halted, the choice output is its ordinary output, so it equals $[\mathrm{true}]$ precisely when that output does. If $c$ is not halted, the choice output is its ordinary output with an extra $[\mathrm{false}]$ appended. Such a list cannot equal the one-element list $[\mathrm{true}]$: equality would force its last element to be both false and true. Thus the choice output is true exactly in the halted case with ordinary output $[\mathrm{true}]$.
