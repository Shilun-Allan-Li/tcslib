<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LargeFourierCoefficient.lean :: FABL.mem_corollary9_32Family -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonempty low-degree family membership

**Claim.** A set $S$ belongs to the family exactly when it is a nonempty subset of the Friedgut coordinates at parameter $1/8$ and its cardinality is at most the corresponding Friedgut degree.

**Proof.** The family is formed from all subsets of the Friedgut coordinates whose cardinality is at most the Friedgut degree, and then the empty set is erased. The membership characterization of the low-degree subsets (`FABL.mem_lowDegreeSubsets`) turns membership before erasure into the conjunction of being a subset of those coordinates and having cardinality at most the degree. Erasing the empty set adds exactly the condition $S \ne \varnothing$, yielding the stated equivalence.

**Key facts.** `FABL.mem_lowDegreeSubsets`.
