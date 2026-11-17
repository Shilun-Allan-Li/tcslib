<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/RandomRestrictions.lean :: FABL.DNFFormula.selectedWidth_le_dimension -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Selected Width Bound

**Claim.** The width of the selected term of a DNF formula is at most the number of coordinates $n$.

**Proof.** The selected term is itself a term on $n$ coordinates. Every such term has width at most $n$ (`FABL.DNFTerm.width_le_dimension`), so the selected term’s width satisfies the same bound.

**Key facts.** `FABL.DNFTerm.width_le_dimension`.
