<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.clockStageCfg_setup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Setup Form of a Halted Clock Configuration

**Claim.** When $c$ is halted, its clock-stage configuration equals the setup configuration formed from itself with reset-start phase, the same input-head position, captured output on the budget tape, an origin-only unary tape, and a blank guide tape with head at zero.

**Proof.** Compare the configuration fields. Since $c.state$ is absent, the clock-stage phase is reset-start, as required. The input position and the original work tapes and their head positions are copied unchanged by the setup construction. On the three added tapes, split into their three possible indices (`finThree_cases`): the budget tape is the captured clock tape of $c.output$; the unary tape agrees with the captured clock tape of the empty word, which is the unary tape of length zero (`clockTape_unary_zero`); and the guide tape is blank. Their head positions are, respectively, $|c.output|+1$, $1$, and $0$ on both sides. Both configurations have empty output, so every field agrees.

**Key facts.** `Complexity.finThree_cases`, `Complexity.clockTape_unary_zero`.
