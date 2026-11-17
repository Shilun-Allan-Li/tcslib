<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.layerGateOf_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a Layered Boolean Gate

**Claim.** Under the stated argument-value correspondence, evaluating the layered gate constructed from $g$ gives the $0$–$1$ encoding of $g$'s evaluation on the Boolean list.

**Proof.** Split according to the gate kind. If $g$ is a NOT gate, well-formedness says its argument list has exactly one entry, say $a$. The layered gate applies $z\mapsto 1-z$ to the value at that entry. By the assumed correspondence, this value is the encoding of the Boolean value at index $a$; the fact that encoding commutes with Boolean negation (`b2f_not`) identifies the result with the encoding of the gate's negated evaluation. If $g$ is an AND gate, its layered operation multiplies the encoded values at all argument positions. The correspondence applies at each position, so the product is the product of the encodings of the corresponding Boolean list values. The product-to-encoded-conjunction identity (`prod_b2f_getElem`) identifies this with the encoding of the AND gate's evaluation. The remaining case would make $g$ an OR gate, which contradicts the hypothesis that its kind is not OR.

**Key facts.** `BoolCircuit.b2f_not`, `BoolCircuit.prod_b2f_getElem`.
