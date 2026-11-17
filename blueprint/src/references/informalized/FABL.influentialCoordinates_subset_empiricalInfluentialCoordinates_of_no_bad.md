<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequences.lean :: FABL.influentialCoordinates_subset_empiricalInfluentialCoordinates_of_no_bad -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empirical Detection of Influential Coordinates

**Claim.** Under the stated monotonicity, total-influence, and sample-accuracy hypotheses, every coordinate whose Boolean influence is at least the prescribed threshold is included in the empirical set of influential coordinates.

**Proof.** For each coordinate $i$, use the sample indexed by its singleton query; that query is available because each singleton belongs to the prescribed family (`FABL.singleton_mem_singletonFourierFamily`). The no-bad-sample hypothesis says its empirical Fourier coefficient differs from the true coefficient by less than the prescribed accuracy. The cast identity identifies the rational empirical coefficient used by the algorithm with the real empirical coefficient for these labeled samples (`FABL.empiricalFourierCoeff_cast`).

Now let $i$ have Boolean influence at least the threshold. Membership in the influential-coordinate set means exactly this inequality (`FABL.mem_influentialCoordinates`). Monotonicity identifies the true singleton Fourier coefficient with the Boolean influence (`FABL.fourierCoeff_singleton_eq_booleanInfluence_of_monotone`). The empirical coefficient is therefore at least the threshold minus the accuracy, so $i$ is selected by the uncapped empirical rule.

Conversely, any coordinate selected by that rule has Boolean influence at least half the threshold: its empirical coefficient is at least threshold minus accuracy, its error from the true coefficient is less than accuracy, and the accuracy is at most one quarter of the threshold (`FABL.singletonInfluenceAccuracy_le_quarter_threshold`). The same monotone singleton-coefficient identity converts this into the influence bound. Thus the uncapped empirical set is contained in the set of coordinates with influence at least half the threshold. The total-influence hypothesis bounds the size of that latter set by the prescribed coordinate cap (`FABL.card_halfThresholdInfluentialCoordinates_le`). Consequently the cap does not discard any selected coordinate, and every coordinate from the original threshold set remains in the empirical set.

**Key facts.** `FABL.singleton_mem_singletonFourierFamily`, `FABL.empiricalFourierCoeff_cast`, `FABL.mem_influentialCoordinates`, `FABL.fourierCoeff_singleton_eq_booleanInfluence_of_monotone`, `FABL.singletonInfluenceAccuracy_le_quarter_threshold`, `FABL.card_halfThresholdInfluentialCoordinates_le`.
