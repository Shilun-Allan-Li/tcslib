<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_observed_action -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Observed Transition Matches Native Step

**Claim.** For record data read from a nonhalted configuration in the specified window, the recorded action agrees with the machine's native one-step action and output, and its outside flag is false exactly when the successor remains in the window.

**Proof.** Because the configuration is not halted, write its state as $q$. The data-reading construction records each scanned work-tape symbol, so its symbol tuple equals the configuration's tuple of scanned symbols. Consequently the action prescribed by the record is precisely the transition of $M$ at state $q$, on the configuration's input symbol and scanned work symbols. Applying that action gives the native successor; its output is likewise the transition's output, which is the machine's output symbol on this live configuration.

Now use the window criterion `recordStep_window` for the native action. Since the starting configuration is in the window, the successor remains in it exactly when no work head at the left edge moves farther left and no work head at the right edge moves farther right. The recorded edge flags identify precisely those boundary heads, and the recorded action supplies their movements. Thus the criterion says exactly that no witness to the outside flag exists, which is equivalent to that Boolean flag being false.

**Key facts.** `Turing.recordStep_window`.
