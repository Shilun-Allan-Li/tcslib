<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Parity.lean :: BoolCircuit.parityCircuit_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity circuit size bound

**Claim.** For every natural number $n$, the size of the parity circuit on $n$ Boolean variables is at most $32(n+1)^4$.

**Proof.** The circuit has maximum fanin at most $2$ (`parityCircuit_maxFanin_le`), so the general size-versus-depth bound gives its size plus one at most $2^{\mathrm{depth}+1}$ (`TreeCircuit.size_succ_le_two_pow`). Its depth is at most $4(\log_2 n+1)$ (`parityCircuit_depth_le`), hence its size is at most $2^{4(\log_2 n+1)+1}$. To bound this expression, first use the elementary estimate $2^{\log_2 n+1}\le 2(n+1)$. Raising both sides to the fourth power and multiplying by $2$ yields
\[
2^{4(\log_2 n+1)+1}=2\bigl(2^{\log_2 n+1}\bigr)^4\le 2\bigl(2(n+1)\bigr)^4=32(n+1)^4.
\]
Combining these inequalities proves the claimed size bound.

**Key facts.** `BoolCircuit.parityCircuit_depth_le`, `BoolCircuit.TreeCircuit.size_succ_le_two_pow`, `BoolCircuit.parityCircuit_maxFanin_le`.
