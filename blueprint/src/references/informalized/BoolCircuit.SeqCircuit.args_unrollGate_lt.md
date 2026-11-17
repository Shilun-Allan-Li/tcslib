<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/SequentialCircuit.lean :: BoolCircuit.SeqCircuit.args_unrollGate_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Argument Bound in an Unrolled Circuit

**Claim.** Every vertex index among the arguments of the gate at position $p$ in the unrolled circuit is less than $n+p$.

**Proof.** Write $p=M.size\,q+m$, where $q=p/M.size$ and $m=p\%M.size$. If $m<r$, the gate is either an initial-register gate with no arguments, or a register-update gate with the single argument obtained by placing the corresponding next-state vertex at stage $q-1$. In the latter case $q>0$, and the next-state vertex is a valid vertex of the original circuit. The placement bound ($M.place_lt$) puts this argument below $n+q\,M.size$; since $m\ge 0$, this is at most $n+p$. If $m\ge r$, the gate comes from a combinational gate, and each of its original arguments is below the original circuit's vertex bound. Placing such an argument at stage $q$ bounds it by $n+(q+1)M.size$. Since $m\ge r$ and $M.size=r+\mathrm{length}(M.comb.gates)$, this is at most $n+p$. If the combinational-gate lookup falls beyond the gate list, the default gate has no arguments. These cases establish the claimed strict bound.

**Key facts.** `BoolCircuit.SeqCircuit.place_lt`.
