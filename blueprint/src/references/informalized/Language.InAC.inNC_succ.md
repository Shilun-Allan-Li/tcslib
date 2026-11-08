<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/NCAC.lean :: Language.InAC.inNC_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# AC depth converted to bounded fan-in

**Claim.** If a language is recognized by a well-formed polynomial-size circuit family with polylogarithmic depth exponent $d$, then it is recognized by a family of fan-in-two circuits with polynomial size and polylogarithmic depth exponent $d+1$.

**Proof.** Take a circuit family witnessing the AC hypothesis, with size bound $a(n+1)^k$ and depth bound $b(\lfloor\log_2 n\rfloor+1)^d$. Replace each circuit by its binarization. This preserves its computed function (`DAGCircuit.binarize_eval`) and gives fan-in at most two (`DAGCircuit.binarize_isFaninTwo`). Its size is at most $n+g(n)(S(n)+2)$, where $g(n)$ is the original gate count and $S(n)$ its size (`DAGCircuit.binarize_size_le`). Since both $n$ and $g(n)$ are at most $S(n)$, this is at most $S(n)(S(n)+2)$; substituting the polynomial size bound and using $(n+1)^k\ge1$ yields the bound $a(a+2)(n+1)^{2k}$. For depth, binarization multiplies the original depth by at most $\operatorname{clog}_2(S(n))+1$ (`DAGCircuit.binarize_depth_le`). The size bound and the logarithmic estimate `BoolCircuit.clog_poly_le` bound this factor by $(a+k+1)(\lfloor\log_2 n\rfloor+1)$. Multiplying by the original depth bound gives $b(a+k+1)(\lfloor\log_2 n\rfloor+1)^{d+1}$. Because binarization preserves evaluation on every input, the new family recognizes the same language, as expressed by the family membership characterization (`DAGCircuitFamily.mem_language_iff`).

**Key facts.** `BoolCircuit.DAGCircuit.binarize_isFaninTwo`, `BoolCircuit.DAGCircuit.binarize_size_le`, `BoolCircuit.DAGCircuit.binarize_depth_le`, `BoolCircuit.clog_poly_le`, `BoolCircuit.DAGCircuit.binarize_eval`, `BoolCircuit.DAGCircuitFamily.mem_language_iff`.
