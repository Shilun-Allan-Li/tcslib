<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.DepthCircuit.exercise4_20b_of_quarterSwitching -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence bound from quarter switching

**Claim.** If a Boolean function is computed by a depth circuit of size at most $s$, then its total influence is at most $4$ times the initial restriction width at size $s$, multiplied by the circuit influence step at size $s+1$ to the power $d-2$.

**Proof.** Choose a witnessing circuit $C$ for the depth and size assumptions, so that $C$ computes the function. The size bound implies both that the tail has at most $s$ internal gates and that the first layer has at most $s$ gates. For each random restriction, the restricted first-layer gates have a maximum width; the expected value of this maximum is at most the initial restriction width at size $s$, by the expected-width estimate for the first layer and monotonicity of that width bound.

Fix a restriction $(J\mid z)$. Every restricted first-layer function has width at most this maximum. Apply the tail influence estimate under the quarter-switching hypothesis to the restricted first-layer functions. The circuit's depth identity, together with the fact that the tail has at least one layer, identifies the exponent in that estimate as $d-2$. Since the tail evaluates these restricted functions to the restricted circuit output, its total influence is at most twice the maximum restricted width times the circuit influence step to that exponent.

Average this pointwise inequality over half-random restrictions. Monotonicity of expectation and the expected-width estimate give an upper bound of twice the influence-step power times the initial restriction width. On the other hand, the expected total influence of a half-random restriction is one half the original total influence. Comparing these bounds and multiplying by two proves the claimed estimate.

**Key facts.** `FABL.DepthCircuit.expect_maxLayer1RestrictedWidth_le`, `FABL.DepthCircuit.initialRestrictionWidth_mono`, `FABL.DepthCircuit.layer1Function_hasWidthLE_extendedSignRestriction_max`, `FABL.CircuitTail.totalInfluence_evalFunction_le_of_quarterSwitching`, `FABL.CircuitTail.extendedSignRestriction_evalFunction`, `FABL.DepthCircuit.evalFunction_layer1`, `FABL.CircuitTail.one_le_layerCount`, `FABL.expectRandomRestriction_mono`, `FABL.expectRandomRestriction_const_mul`, `FABL.expect_totalInfluence_extended_randomRestriction`.
