<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LupanovGates.lean :: BoolCircuit.Lupanov.gateAt_f -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Function block gate formula

**Claim.** For a Boolean function $f$, if $t<2^{2^k}$, the gate at index $o_F(n,k)+t$ is the function gate with bases $n+o_F(n,k)$ and $n+o_Z(n,k)$, parameter $k$, and index parameter $t$.

**Proof.** The offset identities (`offsets`) show that the function block begins after the two heap blocks and that $o_C(n,k)=o_F(n,k)+2^{2^k}$. Hence $o_F(n,k)+t$ is past the input and heap blocks, while the assumed bound places it strictly before $o_C(n,k)$. The circuit definition therefore selects the function-gate branch. Subtracting $o_F(n,k)$ from the index gives its parameter $t$, yielding the asserted gate.

**Key facts.** `BoolCircuit.Lupanov.offsets`.
