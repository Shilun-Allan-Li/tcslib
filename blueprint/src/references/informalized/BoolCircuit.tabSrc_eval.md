<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauCircuit.lean :: BoolCircuit.tabSrc_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of tabulated sources

**Claim.** Under the tabulation invariant at stage $i$, every valid source bit is represented by a vertex whose value equals the source bit’s evaluation on the extended inputs and the program blocks.

**Proof.** Write the tabulation invariant as the prescribed values for the original inputs, the two Boolean constants, the padded input list $z$, and all earlier output blocks. Since $s$ is valid, the conditional in the definition of its assigned vertex takes the valid-source branch. Split into the three source forms. For an input at position $k$, if $k<|z|$, the invariant gives the value stored at the corresponding position in the $z$ portion of the vertex list, which is exactly the value at position $k$ in the concatenated input list. If $k\ge |z|$, the concatenated list instead reads the original input at index $k-|z|$; the input clause of the invariant gives that value as $x(k-|z|)$. For a constant, the assigned vertex is the designated false or true vertex, whose value is fixed by the invariant. For a block bit $(i',j)$, validity gives $i'<i$ and $j<w$, so the earlier-block clause of the invariant identifies its vertex value with bit $j$ of block $i'$ in the program’s output blocks. These cases agree respectively with the three clauses defining source evaluation.
