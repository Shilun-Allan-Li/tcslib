<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/AlmostKWiseAlgorithm.lean :: FABL.almostKWiseOutputList_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the almost-wise output list

**Claim.** The almost-wise output list has length $2^{2d}$, where $d$ is the field degree of its associated small-bias input.

**Proof.** The almost-wise output list is obtained by mapping the transformation over the outputs of the deterministic small-bias algorithm. Mapping a function over a list preserves its length. Those small-bias outputs have length $2^{2d}$ ($\texttt{almostKWiseSmallBiasOutputList\_length}$), which proves the claim.

**Key facts.** `FABL.almostKWiseSmallBiasOutputList_length`.
