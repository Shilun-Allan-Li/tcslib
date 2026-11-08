<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Nondeterministic.lean :: Turing.NDTM.stepWith_eq_fixChoice_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Fixed Choice Gives a Deterministic Step

**Claim.** A nondeterministic step using choice $b$ agrees with one step of the deterministic machine obtained by fixing the choice to $b$.

**Proof.** Split according to whether the configuration's state is empty or is a state $q$. If it is empty, both machines leave the configuration unchanged. If it is $q$, the fixed-choice machine has exactly the transition function of the nondeterministic machine at choice $b$; both therefore apply the same action to the same configuration. In either case the resulting configurations agree.
