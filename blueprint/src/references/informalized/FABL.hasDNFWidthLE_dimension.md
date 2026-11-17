<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.hasDNFWidthLE_dimension -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# DNF width bounded by dimension

**Claim.** Every Boolean function on the \(n\)-dimensional sign cube has a DNF computing it in which each term contains at most \(n\) literals.

**Proof.** Take the DNF supplied by the existence theorem for DNF size and width bounds: it computes the given function, has size at most \(2^n\), and has width at most \(n\) (\(\texttt{FABL.exists_DNFFormula_size_width_bound}\)). Retaining this formula and its width bound gives the required representation.

**Key facts.** `FABL.exists_DNFFormula_size_width_bound`.
