<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Contract.positive_of_not_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Excluding Entry Gives Positive Duration

**Claim.** If the entry state is not in the contract’s exit set, then every admissible start configuration in the entry state has strictly positive contract time.

**Proof.** Fix an admissible start. If its contract time were zero, the zero-time characterization (`Turing.Contract.time_eq_zero_iff`) would imply that the entry state belongs to the exit set, contrary to the hypothesis. Thus the natural-number contract time is nonzero, and every nonzero natural number is strictly positive.

**Key facts.** `Turing.Contract.time_eq_zero_iff`.
