<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.RandomizedDecisionTree.averageCost_le_worstCaseCost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Average Cost Bounded by Worst-Case Cost

**Claim.** For any randomized decision tree and input distribution, its average query cost under that distribution is at most its worst-case query cost over all inputs.

**Proof.** At each input, the cost is bounded by the worst-case cost (`RandomizedDecisionTree.inputCost_le_worstCaseCost`). Monotonicity of finite probability expectation (`pmfExpectation_mono`) carries this pointwise bound to the average over inputs. The expectation of the constant worst-case cost equals the constant (`pmfExpectation_const`), giving the result.

**Key facts.** `FABL.RandomizedDecisionTree.inputCost_le_worstCaseCost`, `FABL.pmfExpectation_mono`, `FABL.pmfExpectation_const`.
