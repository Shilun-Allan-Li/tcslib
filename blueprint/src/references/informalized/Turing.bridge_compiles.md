<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridge_compiles -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Computation by the bridging machine

**Claim.** If a program $c$ sends the singleton containing the sentinel code of each Boolean string $y$ to the singleton containing the sentinel code of $f(y)$, then for every Boolean string $x$ the bridging machine of $c$ has a finite run on input $x$ that halts with output $f(x)$.

**Proof.** Run the encoded program on the sentinel code of $x$. The evaluation-to-machine correspondence for partial-recursive programs, together with the assumed evaluation equation, gives a finite computation of the translated machine from the encoded initial configuration to the halt configuration carrying the sentinel code of $f(x)$. The initial-loading result (\texttt{bridge_start}) brings the bridging machine from its ordinary initial configuration to the configuration representing that encoded initial computation. The simulation theorem (\texttt{bridge_simulate}) transfers each step of the encoded computation to a finite run of the bridging machine, so it reaches the configuration representing the encoded halt result. By the stack-word encoding identity (\texttt{bridgeWord_number}), that result's main stack is the stack word of $f(x)$. The machine then enters its output-emission state; the emission lemma (\texttt{bridge_emit}) shows that it removes the encoded bits from the main stack and appends their Boolean symbols to the output, leaving the machine halted. These finite runs compose by the transitivity of finite reachability (\texttt{bridgeReach_trans}). The equivalence between computation in time and having a halted run with the specified output (\texttt{FinTM.computesInTime_iff}) identifies the endpoint as a computation of $f(x)$.

**Key facts.** `Turing.bridgeWord_number`, `Turing.bridgeCfg_idle`, `Turing.bridgeExec_mem`, `Turing.bridgeReach_trans`, `Turing.bridge_emit`, `Turing.bridge_simulate`, `Turing.bridge_start`, `Turing.bridge_step`, `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_zero`.
