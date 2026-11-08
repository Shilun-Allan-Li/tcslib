<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LupanovGates.lean :: BoolCircuit.Lupanov.eval_or_pair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-input disjunction evaluation

**Claim.** For any natural numbers $a,b$ and Boolean value list $v$, the disjunction gate reading positions $a$ and $b$ evaluates to $v_a\lor v_b$, with out-of-range positions interpreted as false.

**Proof.** The gate’s argument list is $[a,b]$, and its label is disjunction. By the definition of gate evaluation, its value is the disjunction of the values obtained by looking up each argument in the list, using false when a position is out of range. Applying this to the two entries gives $v_a\lor v_b$.
