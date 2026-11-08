<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequencesResources.lean :: FABL.decisionTreeSizeFamilyBound_le_fixed_power -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial bound for the learning family

**Claim.** Under the dimension and precision assumptions, the learning family bound for the decision tree influence parameter is at most the stated constant times the fixed power of $n+1$.

**Proof.** The decision tree influence estimate satisfies the sub-square-root regime conditions with parameters $C=d+1$ and $Q$ (`FABL.decisionTreeSizeInfluenceBound_subsqrtRegime`). The general family-bound theorem for that regime (`FABL.learningConsequencesFamilyBound_le_fixed_power`) then bounds the family size by $2^{2E}(n+1)^E$, where $E$ is the family exponent at $(d+1,Q)$. By definition, the family constant at these parameters is $2^{2E}$, so this is precisely the claimed bound.

**Key facts.** `FABL.decisionTreeSizeInfluenceBound_subsqrtRegime`, `FABL.learningConsequencesFamilyBound_le_fixed_power`.
