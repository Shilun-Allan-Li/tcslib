<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/Program.lean :: FABL.LearningProgram.runWithCost_sequence_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cost Law for a Sequence

**Claim.** For a program followed by a finite list of programs, the run law of the resulting sequence is obtained by first running the initial program, then running the remaining sequence, returning the initial output followed by the tail outputs, and adding the two learning costs.

**Proof.** By the definition of sequence, the initial program is bound to a continuation that maps the remaining sequence's output by placing the initial output at its head. The cost law for binding (`runWithCost_bind`) first expresses this as the law of the initial run followed by that continuation. The cost law for output mapping (`runWithCost_map`) then identifies the continuation's law with mapping the tail run to the list with the head prepended, preserving its cost. Composing these maps combines the two costs by addition and produces the list with the initial output first, as claimed.

**Key facts.** `FABL.LearningProgram.runWithCost_bind`, `FABL.LearningProgram.runWithCost_map`.
