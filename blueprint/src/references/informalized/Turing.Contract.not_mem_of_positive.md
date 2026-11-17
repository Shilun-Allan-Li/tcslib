<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Contract.not_mem_of_positive -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Duration Excludes Entry

**Claim.** If every admissible start configuration in the entry state has strictly positive contract time, then the entry state does not belong to the contract’s exit set.

**Proof.** Suppose, for contradiction, that the entry state belongs to the exit set. The characterization of zero contract time (`Turing.Contract.time_eq_zero_iff`) then implies that the contract time for the given admissible start is zero. This contradicts the assumed strict positivity of that time. Hence the entry state is not an exit.

**Key facts.** `Turing.Contract.time_eq_zero_iff`.
