<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PairEncode.lean :: BoolCircuit.pairEncodeInput_ofFn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Vector for Paired Encoding

**Claim.** The finite vector obtained by evaluating the wiring for the paired encoding of $v$ and $r$ is exactly the paired encoding of the list of values of $v$ and the string $r$.

**Proof.** First, the list of values of the input vector is the wiring list with each wire replaced by its value: a wire selecting an input position $j$ contributes $v(j)$, while a constant wire contributes that constant. This follows by expressing the vector of values as a mapped list of the wiring vector. Unfold the wiring as the vector associated to the pair-wire list; converting that vector back to a list recovers the original list (`BoolCircuit.vectorOfList_ofFn`). The specification of the pair-wire list then identifies the resulting value list with the paired encoding of $\mathrm{List.ofFn}(v)$ and $r$ (`BoolCircuit.pairWireList_spec`).

**Key facts.** `BoolCircuit.vectorOfList_ofFn`, `BoolCircuit.pairWireList_spec`.
