<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathLoops.lean :: Complexity.LogProg.adSite_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Address Column Distinctness

**Claim.** For each address site, column $3$ differs from both columns assigned by the address maps, and the two assigned columns differ from one another.

**Proof.** Split on the form of the address site. For an index site, further split on its index label and on the finite position $j$; for a ten-site, split on its finite position. In each resulting case, the definitions give concrete values in $	ext{Fin }15$, and direct comparison verifies all three inequalities. The double-site case is checked directly from its two assigned values.
