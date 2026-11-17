<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.longCodeExperimentValue_eq_longCodeValue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Experiment value as averaged acceptance

**Claim.** The long-code experiment value equals the uniform average over vertices of the tester's acceptance probability on the averaged-neighbour function.

**Proof.** First express the experiment value as the average over vertices and seeds of the operational check value, using the iterated operational formula (\texttt{FABL.RegularUniqueGame.longCodeExperimentValue\_eq\_iteratedOperational}). For each fixed vertex and seed, the operational check value equals the randomized value of that check on the averaged-neighbour function (\texttt{FABL.RegularUniqueGame.operationalCheckValue\_eq\_randomizedValue}). Averaging this equality over seeds gives the tester's acceptance probability by its definition; averaging over vertices proves the result.

**Key facts.** `FABL.RegularUniqueGame.longCodeExperimentValue_eq_iteratedOperational`, `FABL.RegularUniqueGame.operationalCheckValue_eq_randomizedValue`.
