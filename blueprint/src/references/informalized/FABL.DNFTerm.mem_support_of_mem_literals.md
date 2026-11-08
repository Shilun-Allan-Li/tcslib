<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.DNFTerm.mem_support_of_mem_literals -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Literal Coordinates Lie in the Support

**Claim.** The coordinate of every literal appearing in the term belongs to the term's support.

**Proof.** The support is the set of coordinate indices obtained by mapping the literal list to its indices. Any literal in the list therefore contributes its index to that mapped list, and hence to the support.
