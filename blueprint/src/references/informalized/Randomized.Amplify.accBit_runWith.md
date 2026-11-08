<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyRun.lean :: Randomized.Amplify.accBit_runWith -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance Bit of a Run

**Claim.** For every choice word $l$, the acceptance bit of the configuration reached by running $N$ from its initial configuration on input $x$ under $l$ equals the acceptance bit assigned to $N$, $x$, and $l$.

**Proof.** By definition, the acceptance bit of a configuration is true exactly when the sum of its output list is `some true`. The characterization of this sum says that this happens exactly when the output list is the singleton $[\mathrm{true}]$ (`summ_eq_some_true`). Substituting the definition of the machine's output under choices $l$ gives precisely the definition of the acceptance bit assigned to $N$, $x$, and $l$.

**Key facts.** `Randomized.Amplify.summ_eq_some_true`.
