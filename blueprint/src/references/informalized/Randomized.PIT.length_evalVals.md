<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPEval.lean :: Randomized.PIT.length_evalVals -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the evaluated value list

**Claim.** Evaluating a list of gates in order and appending each gate's value increases the initial value-list length by exactly the number of gates.

**Proof.** Induct on the gate list, generalizing the initial values. With no gates, evaluation returns the initial list, so the length formula holds. For a list beginning with $g$, evaluation first appends the single value of $g$ to the initial list, then evaluates the remaining gates. The induction hypothesis gives the resulting length as the length of this extended list plus the number of remaining gates. Appending one element increases the length by one, yielding $|vs|+|gs|$.
