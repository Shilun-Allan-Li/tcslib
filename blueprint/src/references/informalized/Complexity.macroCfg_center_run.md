<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.macroCfg_center_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Return Scan Prefix

**Claim.** If $n\le R$, then after $n$ schedule steps from the return-to-center phase with guide head at $-R$, the controller remains in the return-to-center phase and the guide head is at $-R+n$.

**Proof.** Induct on $n$. At zero steps the configuration is unchanged. For the successor case, the induction hypothesis gives the return-to-center phase at guide position $-R+n$. The run at the next time is one schedule step from that configuration (`Turing.MultiTapeTM.runFrom_succ_eq_step'`). From $n+1\le R$ we get $n<R$, so $-R+n<0$ and the guide head is not at the origin. The non-origin branch of the return scan step (`Complexity.macroCfg_center`) therefore keeps the controller in that phase and moves the guide head right by one. Its new position is $-R+n+1=-R+(n+1)$, completing the induction.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Complexity.macroCfg_center`.
