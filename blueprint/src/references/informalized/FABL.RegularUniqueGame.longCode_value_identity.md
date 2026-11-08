<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.longCode_value_identity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Long-code value identity

**Claim.** The experiment value equals the uniform average over vertices of the tester's acceptance probability on the function obtained by averaging the permuted neighbouring responses.

**Proof.** The experiment value equals the long-code value by the experiment-to-long-code value identity (\texttt{FABL.RegularUniqueGame.longCodeExperimentValue\_eq\_longCodeValue}). By definition, the long-code value is the uniform average over vertices of the tester's acceptance probability on the averaged-neighbour function. Substituting this definition gives the asserted identity.

**Key facts.** `FABL.RegularUniqueGame.longCodeExperimentValue_eq_longCodeValue`.
