<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PolyTimeModel.lean :: Randomized.polyTimeModel_verifierHasCircuits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuits for Polynomial-Time Verifiers

**Claim.** If the verifier associated to $M$ is efficient, then there are polynomial bounds on circuit size such that, for every input length and every random string of the prescribed length, a well-formed fan-in-two circuit computes $M$ as a function of its input bits.

**Proof.** Choose the accepting language $V_1$ witnessing verifier efficiency. Since $V_1$ is in $	extsf P$, the polynomial-time-to-polynomial-size-circuits theorem supplies a circuit family $F$ deciding it, with size at most $b( ell+1)^j$ for fixed $b,j$ (`Complexity.P_subset_PPoly`). For input length $n$ and fixed random string $r$, take the circuit $C=F(2n+2+|r|)$, which decides membership of the encoded pair consisting of an $n$-bit input and $r$. Encode the fixed string $r$ into the circuit, obtaining $D$. The pair-encoding construction preserves well-formedness and fan-in at most two (`BoolCircuit.DAGCircuit.pairEncode_isFaninTwo`), so $D$ has the required gate properties.

For the size bound, the encoded input length is $ ell=2n+2+|r|$. The hypothesis $|r|=a(n+1)^k$ bounds $ ell+1$ by $(a+3)(n+1)^{k+1}$. Substituting this into the size bound for $C$ and raising to the circuit exponent gives a polynomial in $n$. Increasing the exponent to $(k+1)(j+1)$ also absorbs the extra $n$ input vertices contributed by the encoding. Since the encoded circuit has size $n+|C|$ (`BoolCircuit.DAGCircuit.pairEncode_size`), fixed constants $A=b(a+3)^j+1$ and $K=(k+1)(j+1)$ suffice.

Finally, evaluating $D$ on $v$ is the same as evaluating $C$ on the encoded input pair (`BoolCircuit.DAGCircuit.pairEncode_eval`). The circuit family accepts precisely when that pair belongs to $V_1$ (`BoolCircuit.DAGCircuitFamily.pairEncode_eval_eq_true_iff`), and the verifier witness identifies this membership with $M(v,r)=	ext{true}$. Therefore the circuit output equals $M(v,r)$ for every $v$.

**Key facts.** `Complexity.P_subset_PPoly`, `BoolCircuit.DAGCircuit.pairEncode_isFaninTwo`, `BoolCircuit.DAGCircuit.pairEncode_size`, `BoolCircuit.DAGCircuit.pairEncode_eval`, `BoolCircuit.DAGCircuitFamily.pairEncode_eval_eq_true_iff`.
