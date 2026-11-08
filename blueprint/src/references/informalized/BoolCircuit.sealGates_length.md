<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictSize.lean :: BoolCircuit.sealGates_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length after sealing

**Claim.** Sealing a list of indices adds three gates for each index, so the resulting gate list has length equal to the original length plus three times the number of indices in $L$.

**Proof.** Induct on $L$, generalizing the starting pair $s$. The empty list performs no steps, so its resulting gate list has the original length. For a list with head $u$ and tail $L$, the first sealing step appends the three gates in the sealing triple, increasing the current gate-list length by three. Apply the induction hypothesis to the remaining list starting from this updated pair: it adds a further $3|L|$ gates. The total increase is $3+3|L|=3(|u::L|)$, as required.
