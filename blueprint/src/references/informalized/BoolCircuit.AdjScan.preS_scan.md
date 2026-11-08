<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformAdj.lean :: BoolCircuit.AdjScan.preS_scan -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scan precondition preservation

**Claim.** For every task and valid input, the scan machine satisfies its precondition at every configuration.

**Proof.** If the configuration has no current label, the precondition holds immediately. Otherwise, inspect the current label and the instruction it specifies. The only instructions requiring checks are register-equality tests, input-comparison tests, and calls. The scan uses equality tests only between distinct registers; it uses plain-input comparisons for size and type tasks and paired-input comparisons for the edge task, whose validity hypothesis supplies the required input form. Every call is a read of the first register alone, so its argument list has no repeated registers. All other instructions impose no additional condition, establishing the precondition in every case.
