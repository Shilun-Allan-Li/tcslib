<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Parity.lean :: BoolCircuit.parityCircuit_eval_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-variable parity evaluation

**Claim.** For every assignment $x:\mathrm{Fin}(1)\to\mathrm{Bool}$, the parity circuit on one variable evaluates to $x(0)$.

**Proof.** The general evaluation formula (`BoolCircuit.parityCircuit_eval`) expresses this value as the fold of exclusive-or over the finite range with initial value false. For one variable, that range contains only $0$, so the fold is $\mathrm{Bool.xor}(x(0),\mathrm{false})=x(0)$.

**Key facts.** `BoolCircuit.parityCircuit_eval`.
