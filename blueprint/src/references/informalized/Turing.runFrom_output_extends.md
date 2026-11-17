<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean :: Turing.runFrom_output_extends -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output extends the initial output

**Claim.** After any finite run, the output consists of the initial output followed by some finite word.

**Proof.** Induct on the number of steps, allowing the starting configuration to vary. At zero steps, take the appended word to be empty. For the successor case, express the run as one step followed by the remaining run (`Turing.MultiTapeTM.runFrom_succ_eq_step`) and apply the induction hypothesis to the configuration after that first step. If that configuration is halted, its step leaves it unchanged, so the claimed output decomposition is already the one supplied by induction. Otherwise, its transition appends the output symbol, if any, to the current output. The induction hypothesis appends a further word after that, and associativity of list concatenation combines these into one finite word appended to the original output.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`.
