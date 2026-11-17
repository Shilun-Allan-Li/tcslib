<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequences.lean :: FABL.monotoneBoundedInfluenceRandomExampleProgram_cost_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Learning Program Cost Bounds

**Claim.** Every supported outcome of the program on target $f$ uses at most the monotone bounded-influence random-example budget, makes zero membership queries, and has work at most the corresponding work budget.

**Proof.** Unfold the program's run as a bind of the coordinate-selection stage followed by the Fourier-estimation stage. A supported outcome therefore arises from a supported first-stage outcome and a supported continuation outcome. The selection-stage cost formula (`monotoneInfluenceSelectionProgram_cost_eq`) fixes the first stage's example count, query count, and work. Its selected coordinate set has size at most the coordinate cap (`card_empiricalInfluentialCoordinates_le`); consequently its low-degree Fourier family has size at most the family bound (`card_monotoneSelectedFourierFamily_le`). The family bound is positive (`learningConsequencesFamilyBound_pos`), so the second-stage cost estimate applies: its examples and work are bounded by the family size times the prescribed sample count (and, for work, the extra factor $n+2$), with no queries (`boundedFiniteFamilyFourierEstimatorProgram_cost_le`). Finally, costs add under program bind (`LearningProgram.runWithCost_bind`). Adding the stage bounds gives the stated random-example and work budgets, while both stages use zero queries.

**Key facts.** `FABL.LearningProgram.runWithCost_bind`, `FABL.monotoneInfluenceSelectionProgram_cost_eq`, `FABL.card_empiricalInfluentialCoordinates_le`, `FABL.card_monotoneSelectedFourierFamily_le`, `FABL.learningConsequencesFamilyBound_pos`, `FABL.boundedFiniteFamilyFourierEstimatorProgram_cost_le`.
