<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuit.lean :: Randomized.AlgCircuit.run_append_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution of an Appended Gate

**Claim.** Running a gate list with one gate appended yields the values from running the original list, followed by that gate evaluated using those values.

**Proof.** The fold defining execution first processes the original list, producing its execution-value list. Processing the appended gate then appends its evaluation at that list. Thus the result is the original execution list followed by the single value of the appended gate.
