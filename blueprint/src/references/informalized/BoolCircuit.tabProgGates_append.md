<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauCircuit.lean :: BoolCircuit.tabProgGates_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concatenation Law for Tabulation Gates

**Claim.** The gates tabulated for a concatenation of instruction lists are the concatenation of the gates for the first list and those for the second list, with the second list starting after the first list's length.

**Proof.** Induct on the first instruction list, generalizing the starting position. If it is empty, tabulating the concatenation simply gives the second list's gates at the original position. For a nonempty list, expand the recursive definition at its head and apply the induction hypothesis to the remaining list. Both sides now have the same initial instruction gates and the same appended remainder; the starting index for the second list agrees because the head contributes one position to the first list's length.
