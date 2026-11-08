<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean :: Turing.step_output_prefix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output Prefix after One Step

**Claim.** Prefixing a configuration's output by a finite word before one step has the same effect as prefixing the one-step successor's output afterward.

**Proof.** If the configuration is halted, a step leaves it unchanged, so both sides have the same configuration with output prefixed by $\mathrm{pre}$. Otherwise, the transition depends on the state and the scanned input and work-tape symbols; prefixing the output changes none of these. Thus both configurations use the same action and have the same state, head positions, and tape contents after the step. The action appends its output to the existing output. Associativity of list concatenation then shows that prefixing $\mathrm{pre}$ before this append gives the same output as prefixing it to the successor's output.
