<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicQuery.lean :: FABL.DeterministicQueryProgram.runWithCost_bind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cost of Sequential Programs

**Claim.** For a deterministic query program that returns an output and a continuation assigning a program to each output, sequencing the continuation returns its output and adds its cost to the first program’s cost.

**Proof.** Proceed by induction on the first program. If it immediately returns an output, sequencing simply runs the continuation on that output; the first run has zero cost, so the claimed pair is exactly the continuation’s outcome and cost. If the program makes a batch of queries, both the original and sequenced runs receive the same oracle answers and continue in the corresponding branches. Apply the induction hypothesis to that branch: the continuation’s cost is added to the branch cost, while the batch cost is still charged first. Associativity of addition gives the stated total. If the program charges local work before continuing, both runs charge that same amount and then follow the same continuation; applying the induction hypothesis and reassociating the costs proves the result.
