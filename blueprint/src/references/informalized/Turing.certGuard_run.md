<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CertShell.lean :: Turing.certGuard_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Certificate Guard

**Claim.** After one step, the certificate guard halts and outputs $[\mathrm{false}]$ when the selected tape’s word is empty; when it is nonempty, it reaches the initial configuration with state true.

**Proof.** At the starting configuration, the selected tape’s head is at cell $0$, so the symbol it reads is the value of the buffer tape at $0$. That value is absent exactly when the assigned word is empty. The equivalence between this empty-word condition and the absent symbol is established by inspecting the list’s empty and nonempty cases. The machine’s transition therefore has two cases: for an empty word it writes false to the output and halts; otherwise it leaves tapes, heads, and output unchanged and changes the state to true. Applying that transition gives the stated one-step configuration. The run-after-one-step identity (\texttt{Turing.MultiTapeTM.runFrom\_succ\_eq\_step}) identifies this transition result with the run at time one.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`.
