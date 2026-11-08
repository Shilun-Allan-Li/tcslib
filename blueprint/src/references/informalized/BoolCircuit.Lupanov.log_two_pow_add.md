<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LupanovGates.lean :: BoolCircuit.Lupanov.log_two_pow_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithm of a Power Plus a Remainder

**Claim.** If $p<2^a$, then the base-$2$ logarithm of $2^a+p$ equals $a$.

**Proof.** The quantity $2^a+p$ is at least $2^a$. Since $p<2^a$, it is also less than $2^a+2^a=2^{a+1}$; the equality here is the successor-power identity (`BoolCircuit.Lupanov.two_pow_succ_eq`). Thus the number lies in $[2^a,2^{a+1})$, which characterizes base-$2$ logarithm $a$.

**Key facts.** `BoolCircuit.Lupanov.two_pow_succ_eq`.
