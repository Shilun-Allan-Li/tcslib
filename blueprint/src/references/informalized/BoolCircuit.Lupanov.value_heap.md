<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LupanovGates.lean :: BoolCircuit.Lupanov.value_heap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Values of Heap Gates

**Claim.** Under the stated block and length hypotheses, each heap gate indexed by $1\le q<2^{L+1}$ has value true exactly when the heap path at depth $\lfloor\log_2 q\rfloor$ equals $q$.

**Proof.** Use strong induction on $q$. The gate-position evaluation principle applies because the length hypothesis puts every gate in the specified block within the circuit, and the block hypothesis identifies it as the corresponding heap gate (value_gateAt). If $q=1$, the heap gate is the empty-input AND gate, which evaluates to true; the heap path at depth zero is also $1$. For $q>1$, the gate is a two-input AND: one input is the heap gate indexed by $\lfloor q/2\rfloor$, and the other is the literal recording whether the input bit at offset $o+\lfloor\log_2(q/2)\rfloor$ agrees with the parity of $q$. The first input has the claimed equality interpretation by the strong induction hypothesis; the literal's value is the equality test between the input bit and its specified Boolean value (value_litV). The logarithm identity $\lfloor\log_2 q\rfloor=\lfloor\log_2(q/2)\rfloor+1$ aligns this bit with the last step in the heap-path recursion. Since $q$ is even or odd, its quotient and remainder on division by two determine whether the path's next bit is zero or one. The conjunction is therefore true exactly when the extended heap path equals $q$. The logarithm bound for $q<2^{L+1}$ ensures that all path indices used stay within the stipulated depth range (log_le_of_lt_two_pow_succ).

**Key facts.** `BoolCircuit.Lupanov.value_gateAt`, `BoolCircuit.Lupanov.eval_and_pair`, `BoolCircuit.Lupanov.value_litV`, `BoolCircuit.Lupanov.log_le_of_lt_two_pow_succ`.
