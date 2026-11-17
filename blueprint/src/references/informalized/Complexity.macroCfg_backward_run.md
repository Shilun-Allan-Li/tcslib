<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.macroCfg_backward_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Backward Scan Prefix

**Claim.** If $n\le 2R+1$, then after $n$ schedule steps from the backward phase with guide head at $R$, the controller is still in the backward phase and the guide head is at $R-n$.

**Proof.** Induct on $n$. At $n=0$, the run has not moved, so the claim holds. For the successor case, the induction hypothesis identifies the configuration after $n$ steps with the backward phase at guide position $R-n$. A run of $n+1$ steps is obtained by taking one further step (`Turing.MultiTapeTM.runFrom_succ_eq_step'`). Since $n+1\le 2R+1$, we have $n<2R+1$, and therefore $R-n>-R-1$. The guide head is not at the left-edge position $-R-1$, so the backward scan step (`Complexity.macroCfg_backward`) takes its left-moving branch, keeping the controller in the backward phase. The new guide position is $(R-n)-1=R-(n+1)$, as required.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Complexity.macroCfg_backward`.
