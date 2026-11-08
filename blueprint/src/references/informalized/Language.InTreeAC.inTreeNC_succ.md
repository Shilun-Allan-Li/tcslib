<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeNCAC.lean :: Language.InTreeAC.inTreeNC_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary fan-in tree conversion

**Claim.** A language recognized by polynomial-size circuit trees with depth bounded by a constant times $(\lfloor\log_2 n\rfloor+1)^d$ is recognized by polynomial-size trees of fan-in at most two, with depth bounded by a constant times $(\lfloor\log_2 n\rfloor+1)^{d+1}$.

**Proof.** Take a witnessing tree family, with size bound $a(n+1)^k$ and depth bound $b(\lfloor\log_2 n\rfloor+1)^d$. Replace each tree by its binary conversion. This preserves its Boolean value, gives maximum fan-in at most two, and increases size by at most a factor of three, so the converted family has polynomial size. For depth, the original tree's maximum fan-in is at most its size, hence at most $a(n+1)^k$. The binary-conversion depth bound is the original depth multiplied by at most $\operatorname{clog}_2(a(n+1)^k)+1$. The logarithmic estimate `clog_poly_le` bounds this factor by a constant multiple of $\lfloor\log_2 n\rfloor+1$; multiplying by the original depth bound gives the claimed exponent $d+1$. Since evaluation is preserved on every input, the converted family recognizes the same language.

**Key facts.** `BoolCircuit.toBinary_size_le`, `BoolCircuit.TreeCircuit.maxFanin_le_size`, `BoolCircuit.clog_poly_le`, `BoolCircuit.toBinary_depth_le`, `BoolCircuit.toBinary_maxFanin_le`, `BoolCircuit.toBinary_eval`, `BoolCircuit.TreeCircuitFamily.mem_language_iff`.
