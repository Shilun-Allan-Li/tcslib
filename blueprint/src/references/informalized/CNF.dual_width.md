<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: CNF.dual_width -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width under De Morgan dualization

**Claim.** The width of the De Morgan dual DNF equals the width of the original CNF, with the width of an empty formula taken to be zero.

**Proof.** Dualization maps each clause to a term by flipping its literals. Flipping does not change the number of literals, so each resulting term has exactly the width of its source clause. The dual terms and original clauses occur in corresponding list order, hence taking the maximum of these widths, with zero for an empty list, gives the same value.
