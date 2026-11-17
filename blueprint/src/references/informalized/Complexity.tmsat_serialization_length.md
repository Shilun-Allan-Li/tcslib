<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.tmsat_serialization_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Serialization Length Bound

**Claim.** If the canonizer computes the canonical serialization of the machine decoded from each code within its specified time, then that serialization's length is at most the canonizer's time bound at the code's length.

**Proof.** Apply `computesInTime_iff` to the canonizer's computation on the code. Its output is the serialization of the decoded machine, so the characterization gives the corresponding run's output list. The general output-length bound `output_length_le` says that a machine's output after $t$ steps has length at most $t$. Substituting the canonizer's prescribed time for $t$ yields the desired inequality.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.output_length_le`.
