<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean :: Turing.universal_skip_fixed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact-Cost Skip of Fixed Fields

**Claim.** If the current fixed-field index is $f$ and $f+n=7$, then after $n+1$ steps the interpreter enters the unary-skipping phase, with the table cursor advanced by $n+1$ and the state tape and its cursor unchanged.

**Proof.** Induct on $n$. When $n=0$, the condition forces $f=7$, the last fixed field. The interpreter's transition rule moves the table cursor one place and enters the unary-skipping phase, giving the result in one step. For the induction step, $f$ cannot already be $7$. The transition therefore advances the cursor by one and changes the field index to $f+1$, leaving the other tape data unchanged. The new index satisfies $(f+1)+(n)=7$, so the induction hypothesis applies to the remaining $n+1$ steps from the advanced configuration. Composing the first step with that run gives the claimed total cursor advance and step count. The one-step configuration updates are justified by the interpreter step rule (`Turing.universalEval_step`), and run iteration is unfolded using the successor and zero run identities (`Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`).

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.universalEval_step`.
