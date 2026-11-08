<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.hasDNFSizeLE_DNFsize -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Attainment of minimum DNF size

**Claim.** Every Boolean function on the sign cube has a DNF computing it whose number of terms is at most the minimum possible number of terms among such formulas.

**Proof.** There is at least one admissible term bound: every Boolean function has a DNF with at most \(2^n\) terms (\(\texttt{FABL.hasDNFSizeLE_two_pow}\)). Thus the set of natural-number bounds for which such a DNF exists is nonempty. The infimum of a nonempty set of natural numbers belongs to that set, so a DNF exists with term count at most \(\mathrm{DNFsize}(f)\), as claimed.

**Key facts.** `FABL.hasDNFSizeLE_two_pow`.
