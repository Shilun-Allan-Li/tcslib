<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LupanovGates.lean :: BoolCircuit.Lupanov.gateAt_c -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Combination block gate formula

**Claim.** For any Boolean function $f$ and natural numbers $k,p$, the gate at index $o_C(n,k)+p$ is the combination gate with bases $n+n$ and $n+o_F(n,k)$, parameter $n-k$, code given by $f$ and $k$, and index parameter $p$.

**Proof.** The offset identities (`offsets`) place $o_C(n,k)$ after the input, first heap, second heap, and function blocks. Thus $o_C(n,k)+p$ is not in any of those earlier blocks, and the definition of the circuit selects the combination-gate branch. Its final parameter is $(o_C(n,k)+p)-o_C(n,k)=p$, so the resulting gate is precisely the stated combination gate.

**Key facts.** `BoolCircuit.Lupanov.offsets`.
