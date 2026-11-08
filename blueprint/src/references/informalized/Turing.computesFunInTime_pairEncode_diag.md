<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Encoding.lean :: Turing.computesFunInTime_pairEncode_diag -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear-Time Diagonal Pair Encoding

**Claim.** There is a finite-state Turing machine over the Boolean alphabet and a constant $c$ such that, on every Boolean string $\alpha$, the machine outputs the pair encoding of $\alpha$ with itself within $c(|\alpha|+1)$ steps.

**Proof.** Take the diagonal pair-encoding machine and choose $c=6$. The run lemma identifies its configuration after $4|\alpha|+5$ steps: it has halted and its output is the pair encoding of $\alpha$ with itself (`Turing.pairDiag_run`). Hence it computes the required output in that many steps. Since $4|\alpha|+5\le 6(|\alpha|+1)$ for every natural length, the monotonicity of the computation-time predicate extends this computation to the claimed time bound (`Turing.FinTM.ComputesInTime.mono`).

**Key facts.** `Turing.pairDiag_run`, `Turing.FinTM.ComputesInTime.mono`.
