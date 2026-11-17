<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.DepthCircuit.exercise4_20 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total Influence of a Bounded Circuit

**Claim.** If a Boolean function is computed by a layered circuit of depth $d$, first-layer width at most $w$, and tail size at most $s'$, then its total influence is at most $2w\bigl(20(\lceil\log_2(s'+1)\rceil+2)\bigr)^{d-2}$.

**Proof.** Choose a circuit witnessing the assumed depth, width, tail-size, and function representation. Each first-layer function has width at most the circuit’s width; monotonicity of the width bound (`hasWidthLE_mono`) gives the same bound $w$ for all these functions when viewed as inputs to the tail. The tail influence estimate under the quarter-switching hypothesis (`totalInfluence_evalFunction_le_of_quarterSwitching`) now bounds the total influence of the tail evaluation by $2w$ times the circuit influence step to the power $\mathrm{layerCount}(\mathrm{tail})-1$. The first-layer evaluation followed by the tail is the original circuit function (`evalFunction_layer1`), so this is a bound for the function in question. The tail has at least one layer (`one_le_layerCount`); combining this with circuit depth $d=1+\mathrm{layerCount}(\mathrm{tail})$ identifies the exponent as $d-2$.

**Key facts.** `FABL.CircuitGate.hasWidthLE_mono`, `FABL.DepthCircuit.layer1Function_hasWidthLE`, `FABL.CircuitTail.totalInfluence_evalFunction_le_of_quarterSwitching`, `FABL.DepthCircuit.evalFunction_layer1`, `FABL.CircuitTail.one_le_layerCount`.
