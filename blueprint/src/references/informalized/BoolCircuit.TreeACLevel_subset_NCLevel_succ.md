<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeNCAC.lean :: BoolCircuit.TreeACLevel_subset_NCLevel_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tree Circuit Class Inclusion

**Claim.** Every language in tree circuit class $\mathrm{AC}^i$ belongs to tree circuit class $\mathrm{NC}^{i+1}$.

**Proof.** Take a language in the stated tree circuit class. The general conversion theorem for these classes shows that any language in tree $\mathrm{AC}^d$ also lies in tree $\mathrm{NC}^{d+1}$ (`Language.InTreeAC.inTreeNC_succ`). Applying it with $d=i$ gives the required inclusion.

**Key facts.** `Language.InTreeAC.inTreeNC_succ`.
