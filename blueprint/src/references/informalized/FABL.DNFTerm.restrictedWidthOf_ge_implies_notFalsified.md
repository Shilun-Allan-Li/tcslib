<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/RandomRestrictions.lean :: FABL.DNFTerm.restrictedWidthOf_ge_implies_notFalsified -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive restricted width prevents falsification

**Claim.** If $w>0$ and $w$ is at most the restricted width of a term under a coordinate restriction, then the term is not falsified by that restriction.

**Proof.** Unfold the definition of restricted width and split according to whether some literal is falsified. If such a literal exists, the restricted width is zero, contradicting $0<w\leq 0$. Thus no literal is falsified. By the definition of `notFalsified`, the absence of any falsified literal means its value is true.
