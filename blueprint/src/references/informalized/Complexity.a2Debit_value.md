<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a2Debit_value -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Arithmetic Correctness of Decrement

**Claim.** For every Boolean word $u$, if the fixed-width decrement succeeds, the value of its resulting word plus one equals the value of $u$; if it fails, the value of $u$ is zero.

**Proof.** Induct on the word. The empty word satisfies the claim directly. If the leading bit is true, decrement changes that bit to false and succeeds; the two values differ by exactly one. If the leading bit is false, inspect whether decrement succeeds on the tail. When it does, the induction hypothesis says the decremented tail has value one less than the original tail; placing a false bit before the original tail and a true bit before the decremented tail doubles both tail values, so the required values differ by one. When it fails, the induction hypothesis says the tail has value zero. The original word then also has value zero, since its leading bit is false. These cases establish both alternatives.
