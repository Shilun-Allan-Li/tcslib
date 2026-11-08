<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictCircuit.lean :: BoolCircuit.strictGate_strict -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strictness of a strictified gate

**Claim.** If a gate is well formed and has at most two inputs, its strictification has no repeated inputs and has exactly one input when it is NOT, and exactly two otherwise.

**Proof.** The assumptions provide no repeated original inputs, the one-input condition for NOT gates, and the bound of two inputs. Split by gate kind and input-list length, as in the definition of strictification. When the arguments are mapped through the shift, injectivity of the shift preserves distinctness (`shiftPrefix_injective`). In the one-input AND and OR cases, the added vertex cannot equal the shifted original input, since shifted values are neither $n+1$ nor $n+2$ (`shiftPrefix_ne_one`, `shiftPrefix_ne_two`). The empty AND and OR cases explicitly produce the two distinct added vertices. The remaining cases preserve the original list length under the injective map; the input-count assumptions leave exactly the required lengths for each kind.

**Key facts.** `BoolCircuit.shiftPrefix_injective`, `BoolCircuit.shiftPrefix_ne_one`, `BoolCircuit.shiftPrefix_ne_two`.
