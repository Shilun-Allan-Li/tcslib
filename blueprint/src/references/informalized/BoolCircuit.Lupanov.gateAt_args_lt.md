<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LupanovGates.lean :: BoolCircuit.Lupanov.gateAt_args_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gate inputs precede their gate

**Claim.** For $k\le n$ and any gate index $j$ below the total number of gates, every vertex read by the gate at index $j$ has index less than $n+j$.

**Proof.** Use the size identities for the construction’s blocks (the consequences of the displayed offsets), together with $2^{a+1}=2\cdot 2^a$, to split according to which block contains $j$. For an input negation gate, its only argument is $j<n+j$. In either heap block, the gate is empty when its size parameter is at most one. Otherwise its two arguments are the earlier heap entry and a literal vertex. The logarithmic bound (the fact that $q<2^{a+1}$ implies $\log_2 q\le a$, `log_le_of_lt_two_pow_succ`) bounds the heap level; the literal bound (`litV_le`) bounds the literal vertex. These inequalities put both arguments below $n+j$. In the function block, the zero-parameter gate is empty. Otherwise write its parameter as $t$; the block bound gives $\log_2 t<2^k$. Also $1\le 2^{\lfloor\log_2 t\rfloor}\le t$ (the latter is `Nat.pow_log_le_self`). Substituting these bounds into the two argument formulas shows that each is less than $n+j$. In the final combination block, the first argument is bounded directly from the block index, while the second is $n+o_F(n,k)+\operatorname{code}(f,k,p)$. The bit-list encoding bound (`ofBits_lt`) gives $\operatorname{code}(f,k,p)<2^{2^k}$, so this argument too is below $n+j$.

**Key facts.** `BoolCircuit.Lupanov.two_pow_succ_eq`, `BoolCircuit.Lupanov.log_le_of_lt_two_pow_succ`, `BoolCircuit.Lupanov.litV_le`, `BoolCircuit.Lupanov.ofBits_lt`.
