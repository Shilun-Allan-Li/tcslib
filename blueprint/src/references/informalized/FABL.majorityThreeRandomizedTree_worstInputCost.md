<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.majorityThreeRandomizedTree_worstInputCost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cost on a specified input

**Claim.** On the input $(1,1,-1)$, the randomized decision tree’s expected number of queries is $8/3$.

**Proof.** Apply the formula for the input cost (`majorityThreeRandomizedTree_inputCost`). On $(1,1,-1)$, the first two signs agree, while each of the other two pairs differs. The three pairwise contributions in the formula are therefore $2$, $3$, and $3$, respectively. Their average is $(2+3+3)/3=8/3$.

**Key facts.** `FABL.majorityThreeRandomizedTree_inputCost`.
