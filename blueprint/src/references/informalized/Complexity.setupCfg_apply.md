<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.setupCfg_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Action on a Setup Configuration

**Claim.** Applying the specified action to a setup configuration produces the setup configuration with the prescribed next phase, moved input and controller heads, and optional writes, while preserving the base machine's work tapes, head positions, and output.

**Proof.** Compare the two configurations component by component. The state becomes $q'$, the input head is moved by $d$, and the three controller head positions are incremented by their respective movements. For the tapes, the first $k$ work tapes receive no action and remain those of the base configuration. The three controller tapes are the only remaining cases: each either stays unchanged when no write is prescribed, or is updated at its old head position with the prescribed symbol. The controller tape indices have exactly three possibilities, by the classification of elements of $\mathrm{Fin}(3)$ (`Complexity.finThree_cases`). The action emits no output, so the existing output is preserved. Together these component identities give the stated setup configuration.

**Key facts.** `Complexity.finThree_cases`.
