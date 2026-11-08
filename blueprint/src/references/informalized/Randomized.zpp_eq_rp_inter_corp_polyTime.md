<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PolyTimeModel.lean :: Randomized.zpp_eq_rp_inter_corp_polyTime -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-Error Randomized Time Characterization

**Claim.** For every Boolean-string language $L$, membership in zero-error randomized polynomial time is equivalent to membership in both randomized polynomial time and co-randomized polynomial time, for the polynomial-time verifier model.

**Proof.** Apply the general characterization of zero-error randomized computation (`Randomized.inZPP_iff_inRP_and_inCoRP`) to the polynomial-time verifier model. Its hypotheses are the model's closure under racing two verifiers, under answering with a specified outcome, and under arbitrary verifier constructions. These properties hold for this model by `Randomized.polyTimeModel_closedUnderRace`, `Randomized.polyTimeModel_closedUnderAnswerIs`, and `Randomized.polyTimeModel_closedUnderAny`, respectively. The characterization then gives the stated equivalence for $L$.

**Key facts.** `Randomized.inZPP_iff_inRP_and_inCoRP`, `Randomized.polyTimeModel_closedUnderRace`, `Randomized.polyTimeModel_closedUnderAnswerIs`, `Randomized.polyTimeModel_closedUnderAny`.
