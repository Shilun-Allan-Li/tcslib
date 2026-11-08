<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousLedger.lean :: Complexity.obliviousSchedule_halts -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting time for the schedule

**Claim.** Under the clock hypothesis and $n\le T(n)$, the schedule machine halts on the tagged input by the stated quadratic time bound.

**Proof.** The clock-stage capture lemma (`clockStageCfg_captures`) supplies a time $\tau\le b(T(|x|)+1)$, a halted clock-machine configuration, and the schedule configuration at time $\tau+1$. The binary output represents $T(|x|)$ by `budgetValue_bits`. Its length is bounded by $b(T(|x|)+1)$ using `computesInTime_iff` and the general output-length bound (`MultiTapeTM.output_length_le`). The input-growth hypothesis also gives $|x|+1\le(a+1)(T(|x|)+1)$. The setup lemma (`setupCfg_initializes`) now builds the required initialized configuration, and `clockStageCfg_setup` identifies the captured schedule configuration with its prescribed setup form. The finishing lemma (`setupCfg_finish`) takes that setup through its final phase to a halting state. The run-addition identity (`runFrom_add`) concatenates the clock, initialization, and finishing segments. Finally, the explicit total-time calculation reduces the bound to `obliviousLedger_bound`, with $u=T(|x|)$, $n=|x|$, and the clock output length as the width. This proves both the existence of a halting time and the claimed upper bound.

**Key facts.** `Complexity.clockStageCfg_captures`, `Complexity.budgetValue_bits`, `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.output_length_le`, `Complexity.clockStageCfg_setup`, `Complexity.setupCfg_initializes`, `Complexity.setupCfg_finish`, `Turing.MultiTapeTM.runFrom_add`, `Complexity.obliviousLedger_bound`.
