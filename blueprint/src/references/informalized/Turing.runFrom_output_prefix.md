<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean :: Turing.runFrom_output_prefix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output prefix is preserved

**Claim.** Prefixing a configuration's output by a word before a run has the same effect as prefixing the output after the run; every other component of the resulting configuration is unchanged.

**Proof.** Induct on the run length. At zero steps both sides are the same configuration. For the successor case, rewrite each run as one step followed by the remaining run (`Turing.MultiTapeTM.runFrom_succ_eq_step`). A single step commutes with prefixing the output (`Turing.step_output_prefix`), since the machine appends its transition's output to the existing output. Apply the induction hypothesis to the configuration after that step to commute the prefix through the remaining run. Together these identities give the claimed equality of configurations.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.step_output_prefix`.
