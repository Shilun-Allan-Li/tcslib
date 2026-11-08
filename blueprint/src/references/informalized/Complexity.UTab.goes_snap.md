<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterSteps.lean :: Complexity.UTab.goes_snap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Snapshot instruction transition

**Claim.** Under the stated register conditions, starting at the snapshot template produces the specified output bits and register update, preserves the input position, reaches the copy-loop label when $t=0$ and the layout-processing label otherwise, within the stated step bound.

**Proof.** First, when $t\ne 0$, the snapshot index is at least one stride: since $t\ge 1$, the formula for $\operatorname{snapIdx}$ gives $\operatorname{Str}(M,n,z,T)\le e.i$. This makes the instruction-template transition applicable. The snapshot instruction runs to its successor, updates the instruction index to $e.i+1$, updates the preceding-instruction cell to $0$ for $t=0$ and to $e.i+1-\operatorname{Str}(M,n,z,T)$ otherwise, and leaves the input position unchanged. The instruction-template transition fact supplies this behavior with cost at most $\operatorname{Ki}(M)$ (\texttt{Complexity.UTab.goes_instr_inv}). The identity for the output bits of a snapshot template identifies its printed string with $\operatorname{ibits}(M,n,z,T,e.i)$ (\texttt{Complexity.UTab.snap_bits}).

Next, clear the $lb$ register. The clear-loop fact sends the program from the label indexed by $lb$ to its exit, setting that register to zero, preserving the position, and printing nothing; its cost is $2e.lb+1$ (\texttt{Complexity.UTab.goes_clearR}). Then copy the instruction index into $lb$. Since the scratch register is zero, the copy-loop fact adds the source register to the destination and restores the source, while printing nothing and preserving the position; its cost is $7(e.i+1)+2$ (\texttt{Complexity.UTab.goes_copyR}). Here the source is the updated instruction index, so the new $lb$ value is $e.i+1$.

Concatenating these three transitions gives the required label, registers, position, and appended output. The transition-composition fact adds their step bounds and concatenates their output strings (\texttt{Complexity.CounterProg.Goes.trans}); the final register and bound equalities follow from the stated hypotheses and arithmetic. The total is at most $\operatorname{Ki}(M)+2e.lb+7(e.i+1)+3$.

**Key facts.** `Complexity.UTab.goes_instr_inv`, `Complexity.UTab.snap_bits`, `Complexity.UTab.goes_clearR`, `Complexity.UTab.goes_copyR`, `Complexity.CounterProg.Goes.trans`.
