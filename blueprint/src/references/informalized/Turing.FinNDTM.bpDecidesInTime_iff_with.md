<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTMEquiv.lean :: Turing.FinNDTM.bpDecidesInTime_iff_with -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equivalent bounded-error formulations

**Claim.** Halting within time $T$ and outputting the indicator of $L$ with probability at least $2/3$ on every input is equivalent to the same halting condition with success probability at least the constant function $2/3$.

**Proof.** The two formulations have identical conditions: in the second, the function specifying the lower probability bound is the constant function with value $2/3$. Therefore the defining conjunctions agree directly, giving the equivalence.
