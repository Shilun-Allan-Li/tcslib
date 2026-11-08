<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.RandomizedDecisionTree.sum_queryProbability_eq_averageCost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total query probability equals average cost

**Claim.** For a randomized decision tree and an input distribution with independent coordinates, the sum over coordinates of their query probabilities equals the tree’s average cost.

**Proof.** First interchange the finite sum over coordinates with expectation over inputs. This is valid because expectation here is a finite weighted sum, so summing the coordinatewise expectations is the same as taking the expectation of the sum. For each fixed input, the sum of the probabilities over the random seed that each coordinate is queried equals the expected number of queries on that input: each seed’s query count is the sum of the indicators that each coordinate appears in its query trace. This is the fixed-input identity `sum_queryProbabilityOnInput_eq_inputCost`. Taking expectation over the input distribution therefore gives the average cost.

**Key facts.** `FABL.pmfExpectation_sum`, `FABL.RandomizedDecisionTree.sum_queryProbabilityOnInput_eq_inputCost`.
