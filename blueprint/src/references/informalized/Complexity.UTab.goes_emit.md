<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterMain.lean :: Complexity.UTab.goes_emit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Universal Program Emits the Tableau Circuit

**Claim.** For the specified unary-delimited input and $T\ge1$, the counter program reaches a halted state and prints the encoding of the tableau circuit for $M,n,z,T$ within the stated run bound.

**Proof.** The proof concatenates four runs. First, the input-reading prefix theorem (`goes_prefix`) moves from the initial label to the layer loop, establishes the initial register environment and input position, and prints the circuit's fixed prefix within `prefixBound`. Next, the layer theorem (`goes_layers`) processes the $(T+1)$ tableau layers, reaches the final template label, and prints the encoded layer instructions within its stated layer bound. The template-run theorem (`goes_tp`) executes the final template, whose continuation is the stop label; `goes_stop` then halts without further output. The run-composition theorem (`Goes.trans`) combines these segments, adding their output strings and bounds. The output is the circuit encoding: the prefix and layer output concatenate with the final template output to give the form in `cfgTab_encode`; the linear-operation execution fact (`flatMap_exec_linOps`) identifies the final template's register-generated unary string with the required suffix. Finally, the bound on every template length (`length_tmpl_le`) and the definitions of the prefix and total run bounds show that the sum of the segment bounds is no greater than `runBound`. Thus the combined run has halted, printed exactly the tableau circuit encoding, and respects the claimed bound.

**Key facts.** `Complexity.UTab.goes_prefix`, `Complexity.UTab.goes_layers`, `Complexity.UTab.goes_tp`, `Complexity.UTab.goes_stop`, `Complexity.CounterProg.Goes.trans`, `Complexity.CounterProg.flatMap_exec_linOps`, `Complexity.UTab.cfgTab_encode`, `Complexity.UTab.length_tmpl_le`.
