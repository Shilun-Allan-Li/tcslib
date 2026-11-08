<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satEval_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Linear-Time CNF Evaluator

**Claim.** A finite Boolean Turing machine computes the truth value of any suitably certified CNF formula on the paired encoding of its serialization and assignment word, in a uniform linear time bound.

**Proof.** Choose a machine that extracts the second component of a paired encoding and computes it in time $B(|x|+1)$ (`Turing.FinTM.computesFunInTime_pairSnd`). On the paired input $w$, this machine produces $u$ in time $B(|w|+1)$, since decoding the pair recovers exactly $(\mathrm{enc}(\varphi),u)$ (`Turing.pairDecode_pairEncode`). The evaluator's startup result (`Complexity.satEval_start`) then supplies a saved configuration and a run of length $s$ reaching formula phase at the beginning of the serialization, with $s\le B(|w|+1)+|w|+|u|+5$.

The input has the decomposition into the doubled formula serialization followed by the pair delimiter and $u$. The formula-pass result (`Complexity.satEval_formula`) gives a further run of length $t\le 3|\mathrm{enc}(\varphi)|$ that halts with output $[\varphi(u)]$. Concatenating the startup and evaluation runs using the run concatenation law (`Turing.MultiTapeTM.runFrom_add`) proves that the evaluator computes the required output in $s+t$ steps (`Turing.FinTM.computesInTime_iff`). Finally, the doubled-serialization length identity (`Complexity.satBits_length`) and the length of the paired encoding bound $s+t$ by $(B+6)(|w|+1)$. If necessary, monotonicity of computation time (`Turing.FinTM.ComputesInTime.mono`) extends the computation to that exact bound.

**Key facts.** `Turing.FinTM.computesFunInTime_pairSnd`, `Turing.pairDecode_pairEncode`, `Complexity.satEval_start`, `Complexity.satEval_formula`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.computesInTime_iff`, `Complexity.satBits_length`, `Turing.FinTM.ComputesInTime.mono`.
