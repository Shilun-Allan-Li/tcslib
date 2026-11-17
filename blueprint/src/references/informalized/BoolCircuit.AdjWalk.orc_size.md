<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformWalk.lean :: BoolCircuit.AdjWalk.orc_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oracle Answer for Circuit Size

**Claim.** On the encoding of $1^n$ paired with the binary encoding of $v$, the size oracle returns true exactly when $v$ is less than the size of the circuit for input length $n$.

**Proof.** The size oracle is the Boolean indicator of the size language, so its value is the decision of membership in that language (`indicator_eq_decide`). The size-language membership characterization (`mem_sizeLang`) says that this particular encoding belongs to the language exactly when $v$ is less than the size of the circuit on $n$ inputs. Therefore the oracle returns the decision of that inequality.

**Key facts.** `Complexity.LogProg.indicator_eq_decide`, `BoolCircuit.DAGCircuitFamily.mem_sizeLang`.
