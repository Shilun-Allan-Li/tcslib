<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/AlmostKWiseAlgorithm.lean :: FABL.almostKWiseConstructionWork_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work of the almost-wise construction

**Claim.** The total work of the almost-wise construction is the Vandermonde construction work plus the deterministic small-bias construction work, together with $2^B$ times the matrix-vector multiplication work per output, where $B$ is twice the field degree of the associated small-bias input.

**Proof.** Expand the definition of total construction work. The final traversal contributes its step cost multiplied by the number of outputs, by the fact that traversing a list charges the same work at each entry ($\texttt{binaryConstructorTraversalWork\_eq}$). The number of outputs is $2^{2d}$, where $d$ is the associated small-bias input's field degree ($\texttt{almostKWiseSmallBiasOutputList\_length}$). Finally, the random-bit count is defined to be $2d$, so this factor is $2^B$. Substituting these expressions gives the claimed sum.

**Key facts.** `FABL.binaryConstructorTraversalWork_eq`, `FABL.almostKWiseSmallBiasOutputList_length`.
