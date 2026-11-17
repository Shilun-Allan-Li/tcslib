<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Formulas.lean :: CNF.width_mk -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width of a constructed CNF

**Claim.** The width of the CNF formed from a list of clauses is the maximum clause width in the list, taking the maximum to be zero when the list is empty.

**Proof.** The constructed formula stores exactly the given clause list, and CNF width is defined as the maximum of the widths of its clauses, with zero as the default for an empty list. Substituting the stored list into that definition gives the stated equality.
