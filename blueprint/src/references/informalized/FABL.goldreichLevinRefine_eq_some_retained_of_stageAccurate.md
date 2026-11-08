<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/Controller.lean :: FABL.goldreichLevinRefine_eq_some_retained_of_stageAccurate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successful Accurate Refinement

**Claim.** If the estimates are accurate at stage $k$, then refinement returns the retained candidate family as a successful result.

**Proof.** Stage accuracy, together with the active invariant, bounds the size of the retained family by the active cap (`card_goldreichLevinRetained_le_activeCap_of_stageAccurate`). Refinement returns that family whenever its size is at most the cap. Thus the condition in the refinement rule holds, and its result is the retained family.

**Key facts.** `FABL.card_goldreichLevinRetained_le_activeCap_of_stageAccurate`.
