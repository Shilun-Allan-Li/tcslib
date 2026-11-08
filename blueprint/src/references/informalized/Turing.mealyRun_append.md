<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.mealyRun_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concatenation law for a Mealy run

**Claim.** Running a transition-and-output rule on a concatenation yields the same final state and the concatenation of outputs as running first on the initial string and then on the remaining string from the resulting state.

**Proof.** Induct on the first string, allowing the starting state to vary. If it is empty, running on the concatenation is simply running on the second string, so both the final state and output agree. For a nonempty first string $\gamma::l$, the first transition consumes $\gamma$ and produces its output symbol; the remaining run is on $l++l_2$. Apply the induction hypothesis to that remaining run, starting from the state produced by the first transition. The final states then agree, and the output lists agree because both begin with the first transition's output followed by the concatenated outputs from the induction hypothesis.
