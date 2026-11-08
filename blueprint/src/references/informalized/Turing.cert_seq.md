<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CertShell.lean :: Turing.cert_seq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sequential Composition of Machine Runs

**Claim.** The machine that switches from $M$ to $N$ at the exit of $M$ reaches the right-hand copy of the finish state with tape assignment $w_2$ after $t_0+1+t_1$ steps, and does not visit that state earlier.

**Proof.** The seam-composition run theorem gives the configuration at the stated total time: the first machine reaches its exit configuration after $t_0$ steps, the composition spends one transition switching to the entry state of the second machine, and the second machine then runs for $t_1$ steps to its finish configuration. The seam-composition first-return theorem, using the two hypotheses that their respective exit and finish states are not reached earlier, shows that the right-hand finish state is absent at every earlier time in the composite run. Together these give the claimed pair of conclusions.

**Key facts.** `Turing.seamCompTM_run`, `Turing.seamCompTM_firstReturn`.
