<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean :: BoolCircuit.runWith_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution Over Concatenated Gate Lists

**Claim.** Executing the concatenated gate list $g_s++h_s$ from an initial list $I$ gives the same result as executing $g_s$ from $I$ and then executing $h_s$ from the resulting list.

**Proof.** Execution is a left fold: each gate appends its computed value to the current list. The fold over a concatenation splits into the fold over the first list followed by the fold over the second, with the intermediate list as the second fold's initial state. Thus `runWith_append` holds.
