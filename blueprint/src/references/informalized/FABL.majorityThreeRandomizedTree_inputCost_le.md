<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.majorityThreeRandomizedTree_inputCost_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected Query Cost Bound

**Claim.** For every input $x\in\{-1,1\}^3$, the randomized decision tree's expected number of queries is at most $8/3$.

**Proof.** By the expected-cost formula (\texttt{majorityThreeRandomizedTree\_inputCost}), the cost is the sum of three pair contributions divided by $3$: a pair contributes $2$ when its input signs agree and $3$ otherwise. Among three signs taking only two possible values, at least one pair agrees. Thus at most two contributions are $3$, and the sum is at most $2+3+3=8$. Dividing by $3$ gives the asserted bound.

**Key facts.** `FABL.majorityThreeRandomizedTree_inputCost`.
