<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuit.lean :: Randomized.AlgGate.eval_shift -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of Shifted Gate References

**Claim.** For any input assignment, lists $v,w$ of ring elements, and algebraic gate $g$, evaluating the gate obtained by shifting its node references by $|v|$ on $v$ followed by $w$ gives the same value as evaluating $g$ on $w$.

**Proof.** For every node index $j$, the element at index $j+|v|$ in the concatenated list $v$ followed by $w$ is the element at index $j$ in $w$. Thus their defaulted list lookups agree. A variable gate and the constant gate have no node references, so shifting leaves their evaluations unchanged. Each arithmetic gate uses only the referenced lookups, and these agree by the observation above; consequently its sum, difference, or product evaluation is unchanged as well.
