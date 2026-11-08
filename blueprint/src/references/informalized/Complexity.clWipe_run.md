<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clWipe_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact Scratch Reset Duration

**Claim.** After exactly $2|w|+2$ steps from control state $0$ with the target head at zero, the reset machine reaches control state $2$, with the stream unchanged, the target erased, and the target head at zero.

**Proof.** Split the run into two consecutive blocks, each of length $|w|+1$, using the run-addition law (`Turing.MultiTapeTM.runFrom_add`). The forward-scan result for starting head position zero says the first block reaches control state $1$, leaves the target word intact, and moves its head to $|w|-1$ (`Complexity.clWipe_forward`). Apply the backward-erasing result for the second block: it erases that target word and reaches control state $2$, preserving the stream and returning the target head to zero (`Complexity.clWipe_backward`). The two block lengths add to $2|w|+2$.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Complexity.clWipe_forward`, `Complexity.clWipe_backward`.
