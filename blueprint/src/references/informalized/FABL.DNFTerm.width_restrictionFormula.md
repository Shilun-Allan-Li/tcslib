<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.DNFTerm.width_restrictionFormula -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width after restricting a term

**Claim.** After restricting a term, its width is zero if some literal is falsified by a fixed coordinate; otherwise it is the number of literals whose coordinates remain free.

**Proof.** Split according to whether any literal is falsified. If so, the restriction formula is the empty formula, whose width is zero, and the restricted-width definition also returns zero. If no literal is falsified, the restriction formula consists of the single term obtained by retaining exactly the free-coordinate literals. The width of a one-term formula is that term's width, which is the length of its retained literal list; this is exactly the number specified by the restricted-width definition.
