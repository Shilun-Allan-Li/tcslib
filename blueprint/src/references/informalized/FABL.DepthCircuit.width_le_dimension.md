<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.DepthCircuit.width_le_dimension -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit width bound

**Claim.** For a depth circuit on $n$ coordinates, whose first-layer terms have pairwise distinct literal coordinates, the maximum width of those terms is at most $n$.

**Proof.** The circuit width is the width of the DNF formed by its first-layer terms. The width of a DNF is at most $n$ exactly when every term in it has width at most $n$ (`FABL.DNFFormula.width_le_iff`). Each individual term has pairwise distinct coordinates among its literals, so its width is at most the number of available coordinates, namely $n$ (`FABL.DNFTerm.width_le_dimension`). Applying this to every first-layer term proves the bound.

**Key facts.** `FABL.DNFFormula.width_le_iff`, `FABL.DNFTerm.width_le_dimension`.
