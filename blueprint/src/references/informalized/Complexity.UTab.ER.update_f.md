<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitter.lean :: Complexity.UTab.ER.update_f -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Coordinate Function

**Claim.** For any slot $r$, updating the coordinate function of $e$ at $r$ to $v$ gives the coordinate function of the record obtained by setting slot $r$ to $v$.

**Proof.** Two functions on the eleven slots are equal once their values agree at every slot. Fix a slot $r$ and compare the two functions there. If the queried slot is $r$, both sides have value $v$: the function update assigns $v$, and the record update changes precisely the field represented by $r$. At any other slot, the function update retains the old coordinate, and the record update retains the corresponding field. These coordinate-by-coordinate agreements prove the equality.
