<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/KushilevitzMansour.lean :: FABL.kushilevitzMansourProgram_cost_decomposition -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-stage cost decomposition

**Claim.** Every supported output and cost pair of the Kushilevitz–Mansour run arises from a supported first-stage outcome and a supported second-stage outcome, with the final output equal to the second-stage output and the final cost the componentwise sum of the two costs.

**Proof.** Expand the full program as the bind of the second stage over the Goldreich–Levin query program, and use the run-with-cost rule for a bind (`LearningProgram.runWithCost_bind`). The resulting law first draws an outcome of the query program, then runs the second stage selected by its state, adding the first-stage cost to the second-stage cost. Membership in the support of this bound law therefore gives a first outcome in the support of the query-stage law and a second outcome in the support of the corresponding second-stage law. The bind preserves the second outcome's output, while its cost is the second cost with the first cost added componentwise. Taking these two outcomes gives the asserted output equality and cost decomposition.

**Key facts.** `FABL.LearningProgram.runWithCost_bind`.
