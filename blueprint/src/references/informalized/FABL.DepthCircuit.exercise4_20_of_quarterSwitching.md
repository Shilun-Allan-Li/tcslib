<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.DepthCircuit.exercise4_20_of_quarterSwitching -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total Influence from a Quarter-Switching Bound

**Claim.** Assuming the quarter-switching bound for every positive width, a function computed by a layered circuit of depth $d$, first-layer width at most $w$, and tail size at most $s'$ has total influence at most $2w\bigl(20(\lceil\log_2(s'+1)\rceil+2)\bigr)^{d-2}$.

**Proof.** Choose a circuit witnessing the assumed representation of the function. Each first-layer function has width at most the circuit’s width, and hence at most $w$ by monotonicity (`hasWidthLE_mono` applied to `layer1Function_hasWidthLE`). The tail influence estimate under the quarter-switching assumption (`totalInfluence_evalFunction_le_of_quarterSwitching`) then bounds the total influence of the tail evaluation by $2w$ times the circuit influence step raised to $\mathrm{layerCount}(\mathrm{tail})-1$. The tail evaluation after the first layer is the circuit’s computed function (`evalFunction_layer1`). Since the tail has at least one layer (`one_le_layerCount`) and the circuit depth is one plus the tail’s layer count, this exponent is $d-2$, giving the claimed estimate.

**Key facts.** `FABL.DepthCircuit.layer1Function_hasWidthLE`, `FABL.CircuitGate.hasWidthLE_mono`, `FABL.CircuitTail.totalInfluence_evalFunction_le_of_quarterSwitching`, `FABL.DepthCircuit.evalFunction_layer1`, `FABL.CircuitTail.one_le_layerCount`.
