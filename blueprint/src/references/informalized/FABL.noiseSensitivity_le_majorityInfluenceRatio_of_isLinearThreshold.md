<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/Peres.lean :: FABL.noiseSensitivity_le_majorityInfluenceRatio_of_isLinearThreshold -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise Sensitivity of Linear Thresholds

**Claim.** For a linear threshold function, its noise sensitivity at rate $\delta\in(0,1/2]$ is at most the total influence of majority on $\lfloor1/\delta\rfloor$ variables divided by that number.

**Proof.** The general inverse noise floor bound says that a Boolean class closed under input negations and variable identifications has noise sensitivity at most $A(m)/m$ if every $m$-variable member has total influence at most $A(m)$ (\texttt{noiseSensitivity_le_inverseNoiseFloor_totalInfluenceBound}). Apply it to the class of linear threshold functions, which has both closure properties (\texttt{linearThresholdClass_closedUnderNegatingInputVariables} and \texttt{linearThresholdClass_closedUnderIdentifyingInputVariables}), and take $A(r)$ to be the total influence of $r$-variable majority. For every member $g$ of this class, linear threshold functions are unate (\texttt{isUnate_of_isLinearThreshold}); the influence comparison for unate functions then gives $I[g]\le I[\mathrm{Maj}_r]$ (\texttt{totalInfluence_toReal_le_majority_of_unate}). These hypotheses yield the stated bound with $m=\lfloor1/\delta\rfloor$.

**Key facts.** `FABL.noiseSensitivity_le_inverseNoiseFloor_totalInfluenceBound`, `FABL.linearThresholdClass_closedUnderNegatingInputVariables`, `FABL.linearThresholdClass_closedUnderIdentifyingInputVariables`, `FABL.isUnate_of_isLinearThreshold`, `FABL.totalInfluence_toReal_le_majority_of_unate`.
