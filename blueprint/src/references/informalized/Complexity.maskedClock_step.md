<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean :: Complexity.maskedClock_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Masked Machine Step Correspondence

**Claim.** Masking a configuration after one step of the masked machine gives the same configuration as first masking it and then taking one step of the original machine, including for a halted configuration.

**Proof.** Split according to the state of the configuration $c$. If it is halted, both machines' step rules leave the configuration unchanged, and masking preserves that configuration's data. If its state is $q$, masking preserves the state, so both step rules use the same state $q$. The masked transition function feeds the original transition function the input symbol with each present symbol replaced by $z$; this is exactly the input symbol seen in the masked configuration, by the input-symbol identity (`Complexity.maskedCfg_input`). The work-tape symbols are unchanged by masking. Thus both transitions select the same action. Applying that action commutes with masking (`Complexity.maskedCfg_apply`), giving the claimed equality.

**Key facts.** `Complexity.maskedCfg_input`, `Complexity.maskedCfg_apply`.
