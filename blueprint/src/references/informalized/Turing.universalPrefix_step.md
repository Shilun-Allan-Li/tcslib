<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalStartup.lean :: Turing.universalPrefix_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Prefix Parser Step

**Claim.** If the parser is in state $q$ at input-head position $p$, with output $w$, and the scanned symbol is $b$, then one step gives the configuration prescribed by the transition on $q$ and $b$, with its resulting state, moved head, and appended output.

**Proof.** Because there are no work tapes, the parser’s work-tape contents carry no information. Unfolding the step definition in the live state shows that it applies the transition determined by $q$ and the scanned input symbol. The hypothesis identifies that symbol with $b$. Applying the transition updates the control to its successor state, moves the input head by the prescribed amount, and appends the transition’s optional output to $w$. These are exactly the three fields in the stated configuration; equality follows from extensionality for configurations with no work tapes (`Cfg.ext_zero_tapes`).

**Key facts.** `Turing.Cfg.ext_zero_tapes`.
