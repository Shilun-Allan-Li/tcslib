<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.hasDNFWidthLE_DNFwidth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Attainment of minimum DNF width

**Claim.** Every Boolean function on the sign cube has a DNF computing it whose width is at most the minimum possible width among such formulas.

**Proof.** The set of natural-number width bounds admitting a DNF for \(f\) is nonempty: every Boolean function has a DNF of width at most \(n\) (\(\texttt{FABL.hasDNFWidthLE_dimension}\)). The infimum of a nonempty set of natural numbers belongs to that set. Hence a DNF computing \(f\) exists with width at most \(\mathrm{DNFwidth}(f)\).

**Key facts.** `FABL.hasDNFWidthLE_dimension`.
