<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.macroCfg_forward_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix of the forward scan

**Claim.** If $n\le 2R+1$, then after $n$ steps from the forward phase with guide head at $-R$, the machine remains in the forward phase and its guide head is at $-R+n$.

**Proof.** Induct on $n$. At $n=0$ the configuration is the stated starting configuration. For the successor step, the induction hypothesis places the guide head at $-R+n$. Since $n<2R+1$, this coordinate is strictly less than $R+1$, so it is not the right-edge coordinate. The one-step forward rule (`macroCfg_forward`) therefore keeps the machine in the forward phase and advances the guide head by one. The run successor rule identifies this transition with the next step (`runFrom_succ_eq_step'`), and integer arithmetic gives $-R+n+1=-R+(n+1)$.

**Key facts.** `Complexity.macroCfg_forward`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
