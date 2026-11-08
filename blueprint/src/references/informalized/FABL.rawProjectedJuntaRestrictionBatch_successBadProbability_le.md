<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.rawProjectedJuntaRestrictionBatch_successBadProbability_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bad-Event Probability Under Junta Projection

**Claim.** If an ideal batch of $M$ independent uniform assignments to the free coordinates, labeled by the restriction of the target with the fixed coordinates set to $z$, satisfies the bad property with probability at most $\eta$, then the probability that the projected procedure returns a bad batch is also at most $\eta$. Failure to return a batch is not counted as bad.

**Proof.** Condition first on the entire sequence of fixed-coordinate assignments among the $R$ inputs. If at least $M$ of these assignments equal $z$, the procedure selects $M$ matching indices. The splitting identity `takeMatchingJuntaExamples_from_split` identifies the projected output with the restriction batch formed from the selected free assignments. The selected-batch distribution identity (`map_uniformPMF_selectedJuntaRestrictionBatch`) says that, as the free assignments vary uniformly, this labeled batch has exactly the ideal batch distribution. Thus its probability of being bad is the ideal bad-event probability. If fewer than $M$ fixed assignments match, `takeMatchingJuntaExamples_eq_none_iff` shows that the procedure returns none, which is excluded from the bad event; its conditional bad probability is therefore zero. In either case, the conditional probability is at most the ideal probability. The product decomposition of the uniform input distribution into uniform fixed and free assignments (`map_uniformPMF_rawProjectedJuntaRestrictionBatch`) averages these conditional bounds over all fixed-coordinate sequences, yielding the same bound for the unconditional outer measure. Finally, the ideal event has finite measure (`pmfToOuterMeasure_ne_top`), so monotonicity of conversion to real probabilities and the assumed bound give the result.

**Key facts.** `FABL.takeMatchingJuntaExamples_from_split`, `FABL.map_uniformPMF_selectedJuntaRestrictionBatch`, `FABL.takeMatchingJuntaExamples_eq_none_iff`, `FABL.map_uniformPMF_rawProjectedJuntaRestrictionBatch`, `FABL.pmfToOuterMeasure_ne_top`.
