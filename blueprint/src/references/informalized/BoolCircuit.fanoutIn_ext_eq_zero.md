<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/FormulaFanOut.lean :: BoolCircuit.fanoutIn_ext_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero fan-out in an appended segment

**Claim.** If the concatenation of two gate lists is acyclic and $n+|gs++ext|\le v$, then the fan-out of $v$ within $ext$ is zero.

**Proof.** Acyclicity of the concatenation and the bound on $v$ imply, by the zero-fan-out theorem for an acyclic list (BoolCircuit.fanoutIn_eq_zero_of_le), that the fan-out of $v$ in the whole concatenation is zero. Fan-out is additive under concatenation (BoolCircuit.fanoutIn_append), so this zero equals the sum of the fan-outs in $gs$ and $ext$. Both terms are natural numbers, hence nonnegative, and their sum can be zero only if each term is zero. In particular, the fan-out in $ext$ is zero.

**Key facts.** `BoolCircuit.fanoutIn_eq_zero_of_le`, `BoolCircuit.fanoutIn_append`.
