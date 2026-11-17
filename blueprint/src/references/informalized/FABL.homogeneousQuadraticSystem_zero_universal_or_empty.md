<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.homogeneousQuadraticSystem_zero_universal_or_empty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-Dimensional System Dichotomy

**Claim.** For a finite system of homogeneous quadratic equations in zero variables, either every zero-dimensional Boolean word satisfies every equation or none does.

**Proof.** Consider whether every equation in the system has right-hand side zero. If so, the zero-dimensional satisfaction criterion says that every word satisfies the system. If not, the same criterion shows that no word can satisfy it: any satisfying word would imply that every equation has right-hand side zero, contradicting the chosen case. The criterion used here is that, in dimension zero, system satisfaction is equivalent to every equation’s right-hand side being zero (\texttt{satisfiesHomogeneousQuadraticSystem\_zero\_iff}).

**Key facts.** `FABL.satisfiesHomogeneousQuadraticSystem_zero_iff`.
