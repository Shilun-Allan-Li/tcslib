<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterLayer.lean :: Complexity.UTab.goes_instr_inv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Template Execution Bound

**Claim.** Under the stated conditions on the initial-step flag and the register $q$, executing a template from its label reaches the successor label, preserves the input position, and appends the template operations evaluated at the initial registers. The final record has $i=e.i+1$ and has $q=0$ when $t=0$, or $q=e.i+1-S$ when $t\ne 0$, within the uniform bound $K$ on template execution.

**Proof.** Apply the preceding template-execution result (`goes_instr`) to obtain the claimed output, unchanged input position, and the register update determined by the initial-step flag. The flag hypothesis identifies that flag with whether $t=0$. The uniform length estimate (`length_tmpl_le`) bounds the template-specific step allowance by $K=Lmax+3$, so the execution also satisfies this common bound (`Goes.congr`). It remains to identify the updated registers. If $t=0$, the flag is true, so the instruction counter increases by one while $q$ is unchanged; the hypothesis $e.q=0$ gives the required final value. If $t\ne0$, the flag is false, so both $i$ and $q$ increase by one. Using $e.q=e.i-S$, the new $q$ is $e.i-S+1$. Since $S\le e.i$, natural-number subtraction gives $e.i-S+1=e.i+1-S$, as required. Thus the register update from `goes_instr`, rewritten in the two cases, is exactly the stated final record.

**Key facts.** `Complexity.UTab.goes_instr`, `Complexity.UTab.length_tmpl_le`, `Complexity.CounterProg.Goes.congr`.
