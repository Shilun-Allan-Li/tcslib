<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.cont_pair_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Computation of the encoded pair predicate

**Claim.** The pair-loader machine, on the self-delimiting encoding of $(x,u)$, halts with the single bit indicating whether the run of $N$ on $x$ under choices $u$ halts with output $[1]$, in the stated number of steps.

**Proof.** Write $y$ for the encoding of $(x,u)$. The initial configuration on $y$ is the loader configuration at the beginning of the input, with empty buffers; the proof verifies this by comparing the initial configuration fields. The parser-run lemma consumes the doubled encoding of $x$, taking $2|x|+2$ steps and leaving the loader in state $3$ with $x$ in its input buffer and the choice buffer empty (`Complexity.cont_parse_run`). The suffix-run lemma then processes the delimiter and the choice word, simulates the run determined by $u$, and finishes in the halting state with the specified Boolean output (`Complexity.cont_suffix_run`). Combining these consecutive runs uses the run-addition law (`Turing.MultiTapeTM.runFrom_add`); simplifying the encoding length gives the intermediate time displayed in the proof. The equivalence between computation in time and the final state and output conditions translates this run description into the computation claim (`Turing.FinTM.computesInTime_iff`). Finally, the stated time is at least the intermediate time, so monotonicity of computation time yields the exact claimed bound (`Turing.FinTM.ComputesInTime.mono`).

**Key facts.** `Complexity.cont_parse_run`, `Complexity.cont_suffix_run`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.mono`.
