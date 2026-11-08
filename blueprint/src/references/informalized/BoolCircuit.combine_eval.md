<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeNCAC.lean :: BoolCircuit.combine_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a Combined Circuit

**Claim.** For any gate type, finite list of Boolean circuit trees, and assignment of Boolean values to the variables, combining the list gives the same value as applying the chosen gate directly to the list.

**Proof.** The combined circuit runs the recursive construction with fuel equal to the list length. Apply the evaluation-preservation result `combineFuel_eval` at that fuel and list; it states exactly that the recursive result evaluates as the chosen gate applied directly to the original list.

**Key facts.** `BoolCircuit.combineFuel_eval`.
