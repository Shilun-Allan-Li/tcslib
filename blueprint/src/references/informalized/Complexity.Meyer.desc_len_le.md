<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Meyer.lean :: Complexity.Meyer.desc_len_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit Description Length Bound

**Claim.** Under the stated fan-in and circuit-size bounds, the encoding length plus one of the circuit at input length $n_b+4W(n)+4+n$ is at most $\bigl(12a^2(n_b+4C_w+6)^{2k}+1\bigr)(n+1)^{2(c_w+1)k}$, where $W(n)=C_w(n+1)^{c_w}$.

**Proof.** Set $P=(n+1)^{c_w+1}$ and $K=n_b+4C_w+6$. Since $n+1\ge1$, we have $P\ge1$ and $n+1\le P$. Also $(n+1)^{c_w}\le P$, so $W(n)\le C_wP$. These estimates imply that the input length for the circuit, plus one, is at most $KP$. Applying the assumed size bound at this input length, and then monotonicity of powers, bounds the circuit size by $aK^kP^k$. The fan-in-two encoding estimate says that the encoding length is at most twelve times the square of the circuit size (`length_encode_le_of_isFaninTwo`). Squaring the size bound and adding one therefore gives at most $12(aK^kP^k)^2+1$. Finally, $P^{2k}=(n+1)^{2(c_w+1)k}$; the remaining constant and polynomial factors are bounded by the claimed right-hand side, using that this power is at least one.

**Key facts.** `BoolCircuit.DAGCircuit.length_encode_le_of_isFaninTwo`.
