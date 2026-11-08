<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/Program.lean :: FABL.LearningProgram.map_addOutcomeCost_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero cost preserves the law

**Claim.** Mapping a probability mass function on output-and-cost pairs by adding zero to each cost leaves the law unchanged.

**Proof.** Adding zero to a learning cost leaves every outcome-and-cost pair unchanged (\texttt{addOutcomeCost\_zero}). Thus the map being applied is the identity function, and mapping a probability mass function by the identity leaves it unchanged.

**Key facts.** `FABL.LearningProgram.addOutcomeCost_zero`.
