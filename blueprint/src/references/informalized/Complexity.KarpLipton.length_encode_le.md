<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLipton.lean :: Complexity.KarpLipton.length_encode_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit encoding length bound

**Claim.** Under the fan-in and size bounds on the circuit family, the encoded circuit for input length $q(C,c,x)$ has the stated polynomial length bound.

**Proof.** Set $n=|x|$ and $P=(n+1)^{c+1}$. Since $n+1\le P$ and $(n+1)^c\le P$, the definition of $q$ gives $q(C,c,x)+1\le (8+3C)P$. The size hypothesis applied at this input length, followed by monotonicity of powers, yields $\mathrm{size}(F_{q})\le a(8+3C)^kP^k$. The encoding bound for fan-in-two circuits (\texttt{BoolCircuit.DAGCircuit.length_encode_le_of_isFaninTwo}) says its encoding length is at most twelve times the square of its size. Applying this bound and adding one gives an upper bound of $12(a(8+3C)^kP^k)^2+1$. Finally, $P^{2k}=(n+1)^{2(c+1)k}$; expanding the square gives the claimed coefficient and exponent, with the added one absorbed using $(n+1)^{2(c+1)k}\ge1$.

**Key facts.** `BoolCircuit.DAGCircuit.length_encode_le_of_isFaninTwo`.
