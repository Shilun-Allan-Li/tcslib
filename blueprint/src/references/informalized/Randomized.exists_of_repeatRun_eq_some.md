<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ExpectedTime.lean :: Randomized.exists_of_repeatRun_eq_some -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Successful Block in a Repeated Run

**Claim.** If a repeated run on a Boolean list returns a value $a$, then some Boolean list of length exactly $t$ is sent to $a$ by the underlying procedure.

**Proof.** Use strong induction on the length of the input list. If the repeated-run definition is active, then $0<t$ and the list has length at least $t$. By the repeated-run decomposition (`Randomized.repeatRun_of_le`), the result comes from the first block, the prefix of length $t$, or from recursively repeating the procedure on the remaining suffix. In the first case, that prefix has length exactly $t$ and already returns $a$. In the second case, the recursive result is still $a$; the suffix is shorter than the original list, so the induction hypothesis supplies a length-$t$ list on which the procedure returns $a$. If the definition is inactive, the repeated run is none, contradicting that it returned some value.

**Key facts.** `Randomized.repeatRun_of_le`.
