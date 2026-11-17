<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepClock.lean :: Turing.sc_live -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Nonstopped Configuration Is Live

**Claim.** If a configuration is not stopped, its state is present and its stopping predicate is false.

**Proof.** Split on whether the configuration's state is absent or is some state $s$. An absent state would make the configuration stopped, contradicting the hypothesis. Thus its state is $s$. Since the predicate is Boolean, it is either false or true; the true case would also make the configuration stopped. Therefore it is false, as claimed.
