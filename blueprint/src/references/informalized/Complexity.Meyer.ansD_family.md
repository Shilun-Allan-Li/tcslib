<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerSigma.lean :: Complexity.Meyer.ansD_family -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit Family Computes Simulation Queries

**Claim.** For width-$W$ counters encoding $t,a<2^W$, the specified circuit-family query returns the tabulated answer for the selected component after $t$ machine steps, with counter value $a$.

**Proof.** First, the query formed from the selector encoding, the width-$W$ encodings of $t$ and $a$, and $x$ has tabulation value equal to the desired answer. Indeed, `tabFun_query` reduces that value to the answer after $\operatorname{ctrVal}$ of each counter word, and `ctrVal_enumWord` identifies those values as $t$ and $a$. The query's length is $n_{\mathrm{bits}}(M)+4W+4+|x|$, by the lengths of its encoded fields.

Because the circuit family has fan-in at most two, `query_mem_CVAL_iff` says that the pair consisting of the circuit description at this input length and the query belongs to the circuit-value language exactly when the query is accepted by the family. The equality of that language with the tabulation language identifies this membership test with whether the query's tabulation value is true. Finally, the bounds on $t$ and $a$ ensure `wordOf` returns their width-$W$ encodings, so the circuit-based answer equals the required tabulated answer.

**Key facts.** `Complexity.Meyer.tabFun_query`, `Complexity.Meyer.ctrVal_enumWord`, `Complexity.Meyer.query_mem_CVAL_iff`, `Complexity.Meyer.wordOf_of_lt`.
