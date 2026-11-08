<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean :: BoolCircuit.runWith_eq_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Appended gate outputs

**Claim.** For any gate list and initial value list, successively evaluating the gates produces the initial list followed by some list of outputs.

**Proof.** Induct on the gate list, allowing the initial list to vary. With no gates, the result is the initial list, so take the appended list to be empty. For a first gate $g$, the execution rule (`runWith_cons`) first appends the value of $g$ on the initial list and then executes the remaining gates. Apply the induction hypothesis to those remaining gates starting from this extended list. The final result is the original initial list followed by the first gate’s output and then the remaining appended outputs; associativity of list concatenation gives the asserted form.

**Key facts.** `BoolCircuit.runWith_cons`.
