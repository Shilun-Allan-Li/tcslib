<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/NCAC.lean :: Language.InNC.inTreeNC_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# NC Circuits Have Tree Representations

**Claim.** A language recognized by a well-formed fan-in-two circuit family of polynomial size and depth at most $b(\lfloor\log_2 n\rfloor+1)$ has a polynomial-size tree representation of fan-in at most two and depth bounded by a constant times $\lfloor\log_2 n\rfloor+1$.

**Proof.** Choose a circuit family $C$ witnessing the hypothesis. Fan-in two supplies both well-formedness and the bound of two on each gate's number of inputs (`BoolCircuit.DAGCircuitFamily.HasFaninTwo.isWellFormed`). Expand each circuit into a tree. The expansion preserves the language (`BoolCircuit.DAGCircuitFamily.language_toTree`), has fan-in at most two (`BoolCircuit.DAGCircuit.toTree_maxFanin_le`), and has depth at most the original depth (`BoolCircuit.DAGCircuit.toTree_depth_le`). Its size is at most $(2+1)^d=3^d$, where $d$ is the circuit depth (`BoolCircuit.DAGCircuit.toTree_size_le`). Set $q=\lfloor\log_2 n\rfloor+1$. Since $d\le bq$, the tree size is at most $3^{bq}=(3\cdot3^{\lfloor\log_2 n\rfloor})^b$. The estimate $3^{\lfloor\log_2 n\rfloor}\le(n+1)^2$ (`BoolCircuit.three_pow_log_le`) bounds this by $3^b(n+1)^{2b}$. Thus the tree family has polynomial size. Its depth is at most $bq$, the original bound, so it also has the required logarithmic-depth bound.

**Key facts.** `BoolCircuit.DAGCircuitFamily.HasFaninTwo.isWellFormed`, `BoolCircuit.DAGCircuit.toTree_maxFanin_le`, `BoolCircuit.DAGCircuit.toTree_size_le`, `BoolCircuit.DAGCircuit.toTree_depth_le`, `BoolCircuit.three_pow_log_le`, `BoolCircuit.DAGCircuitFamily.language_toTree`.
