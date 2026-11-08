<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.recursiveNandRandomizedTree_worstCaseCost_le_maxOutputCost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Worst-Case Cost from Output-Conditioned Costs

**Claim.** For every $d$, the worst-case expected query cost of the level-$d$ randomized tree is at most the larger of its two output-conditioned costs, one for output $+1$ and one for output $-1$.

**Proof.** The worst-case cost is the supremum of the input cost over all inputs. Fix any input. Since a sign-valued output is either $+1$ or $-1$, split into these two cases. When the output is $+1$, the input cost is at most the output-conditioned cost for $+1$ (\(\texttt{FABL.RandomizedDecisionTree.inputCost_le_outputConditionalCost}\)), hence at most the maximum of the two conditioned costs. When the output is $-1$, the same input-cost bound for that output gives the other side of the maximum. Thus every input cost is bounded by this maximum, and so is their supremum.

**Key facts.** `FABL.RandomizedDecisionTree.inputCost_le_outputConditionalCost`.
