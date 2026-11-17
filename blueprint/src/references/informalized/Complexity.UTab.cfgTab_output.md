<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterMain.lean :: Complexity.UTab.cfgTab_output -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Configuration tableau output index

**Claim.** The output vertex of the configuration-tableau circuit is the current snapshot's encoded output-bit position, expressed as a linear expression evaluated on the registers at time $T+1$ with loop counter zero.

**Proof.** The circuit selects the snapshot block at time $T$ and the bit position equal to the snapshot width. The index bound \texttt{snapIdx\_lt\_succ}, together with the program-length and input-layout length formulas (\texttt{length\_cfgProg} and \texttt{length\_tabLayout}), shows that this requested block and bit are within the tableau program and its output width. Thus the conditional output formula for the tableau circuit takes its valid-index branch, giving the selected block's base plus the fixed offset for the snapshot output bit. For the linear expression associated to the current source, its register list consists of the input-count register, the hard-wired-length register, and one copy of the current-instruction register for each gate in a tableau block. Evaluating it at the registers of \texttt{lstart} at time $T+1$ reduces these terms to the corresponding block offset and constants. The index identity $\operatorname{snapIdx}(T)+1=(T+1)\operatorname{Str}(M,n,z,T)$ then identifies this value with the selected output index; the remaining equality is arithmetic simplification.

**Key facts.** `Complexity.length_cfgProg`, `Complexity.length_tabLayout`, `Complexity.snapIdx_lt_succ`, `Complexity.UTab.ER.f_i`, `Complexity.UTab.ER.f_nc`, `Complexity.UTab.ER.f_z`.
