<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.RandomizedDecisionTree.inputCost_le_outputConditionalCost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Cost and Conditional Cost

**Claim.** If an input produces the output value $a$, its expected query count is at most the maximum, over all inputs, of the expected query count on inputs producing $a$, with value zero assigned to other inputs.

**Proof.** At the given input $x$, the condition $f(x)=a$ makes the conditional-cost expression equal to the input cost at $x$. The supremum over all inputs is at least the value of that expression at this particular input, since $x$ belongs to the full input space. This is exactly the asserted inequality.
