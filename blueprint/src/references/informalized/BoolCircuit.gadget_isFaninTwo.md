<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyGadget.lean :: BoolCircuit.gadget_isFaninTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fan-In Bound for the Gadget

**Claim.** For every natural number $m$ and Boolean function $f$ on assignments to $m$ variables, the gadget constructed from $f$ is well formed and every gate has at most two inputs.

**Proof.** The gadget is defined by binarizing the DAG translation of the universal tree circuit, using the well-formedness of that translation. The binarization theorem states that binarizing any well-formed DAG produces a circuit that is well formed and whose gates each have at most two inputs. Applying it to this tree-derived DAG gives the claim.

**Key facts.** `BoolCircuit.DAGCircuit.binarize_isFaninTwo`.
