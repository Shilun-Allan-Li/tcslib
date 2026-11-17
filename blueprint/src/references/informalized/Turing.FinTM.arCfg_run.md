<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean :: Turing.FinTM.arCfg_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulation Over Multiple Cycles

**Claim.** After $(3(N+1)+2)t$ steps, the binary block-code simulator reaches the encoding of the configuration obtained after $t$ steps of the original machine.

**Proof.** Proceed by induction on $t$. At $t=0$, running for zero steps leaves the initial encoded configuration unchanged (`Turing.MultiTapeTM.runFrom_zero`). For the induction step, split the $(t+1)$-cycle run into the first $t$ cycles and one further cycle, using the addition law for runs (`Turing.MultiTapeTM.runFrom_add`). By the induction hypothesis, the first part reaches the encoding of the original machine's configuration after $t$ steps. The one-cycle simulation lemma (`Turing.FinTM.arCfg_cycle`) then identifies the next $(3(N+1)+2)$ simulator steps with encoding one original machine step. The successor-run identity (`Turing.MultiTapeTM.runFrom_succ_eq_step'`) identifies that configuration with the original machine's run after $t+1$ steps, completing the induction.

**Key facts.** `Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.arCfg_cycle`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
