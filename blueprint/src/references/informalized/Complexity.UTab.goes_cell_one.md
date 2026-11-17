<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterLayer.lean :: Complexity.UTab.goes_cell_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulation of a Work-Cell Template

**Claim.** Under the stated register, position, time, and phase hypotheses, executing the template for the specified work cell reaches its following label, updates the instruction and preceding-cell registers as stated, leaves the input position unchanged, appends the instruction bits for the current position, and takes at most $L_{\max}(M)+3$ steps.

**Proof.** Let $S=\mathrm{Str}(M,n,z,T)$, which is the stride $\mathrm{cfgStride}(M,z.length+n,T)$. The index formula and $t\ne0$ imply $S\le e_i$: the time contribution $tS$ is at least $S$, and the other terms in the cell index are nonnegative. Thus, when $t\ne0$, the hypothesis $e_q=e_i-S$ is consistent with the preceding cell being one stride earlier, namely $e_q+S=e_i$.

Apply the inverse template-simulation result `goes_instr_inv` to the cell template. Its hypotheses are supplied by the template’s time-zero flag, the assumed value of $e_q$, and the stride lower bound just proved. It says that the program executes the template’s operations and reaches the template’s designated successor, updating $e_i$ to $e_i+1$ and $e_q$ to $0$ at time zero or $e_i+1-S$ otherwise, while preserving the input position; the step count is at most $\mathrm{Ki}(M)=L_{\max}(M)+3$. Finally, `cell_bits` identifies the bits emitted by executing this template with the instruction bits at position $e_i$. Its hypotheses are exactly the cell-position, register, stride, and phase agreements in the statement, with the stride identity above supplying its preceding-cell condition. Substituting this identification gives the claimed output.

**Key facts.** `Complexity.UTab.goes_instr_inv`, `Complexity.UTab.cell_bits`.
