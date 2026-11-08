<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterSteps.lean :: Complexity.UTab.goes_layers -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution through all tableau layers

**Claim.** The counter program runs from the initial layer-start configuration to the final-template label with the specified final registers and input position, appending the instruction-bit strings for all indices from $0$ through $(T+1)D-1$ within the stated step bound.

**Proof.** First apply the one-layer execution result at $t=0$. Since this is the initial layer, it reaches the copy loop; the register identity for the successor layer (`lstart_succ`) identifies its endpoint with the start configuration needed for copying. The right-copy procedure (`goes_copyR`) then reaches the layer-loop head, adds the value of the source counter to the destination counter, and takes at most $7T+2$ steps. In this initial case the source value is $T$, so the loop counter is set to $T$ as required.

Next, use the general loop theorem (`goes_loop`) for the layer loop. Its counter is $T-j$ after $j$ iterations. For each $j<T$, the body is exactly the one-layer execution at layer $j+1$; its endpoint is the next loop head with the counter decreased by one. Thus the loop executes all remaining $T$ layers, exits at the final-template label, and appends the concatenation of their layer outputs. Together with the initial layer, these outputs cover the consecutive blocks beginning at $0,D,\ldots,TD$. The range decomposition (`range_mul`) identifies their concatenation with the required range of length $(T+1)D$.

Compose the initial layer, the copy procedure, and the loop. The resulting register and label descriptions agree with the theorem’s endpoints after the recorded layer-start identities are simplified. The total cost is bounded by $(T+1)(\mathrm{layerBound}+7T+10)$: the one initial layer costs at most `layerBound`, copying costs at most $7T+2$, and the loop costs at most $T(\mathrm{layerBound}+2)$, which together are no larger than the stated bound.

**Key facts.** `Complexity.UTab.goes_layer`, `Complexity.UTab.lstart_succ`, `Complexity.UTab.goes_copyR`, `Complexity.CounterProg.Goes.congr`, `Complexity.UTab.goes_layer`, `Complexity.CounterProg.goes_loop`, `Complexity.CounterProg.Goes.trans`, `Complexity.UTab.range_mul`.
