<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalK.lean :: Turing.EffectiveMachineCode2.toK_toFinTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement of Machine Conversions

**Claim.** For an effective two-work-tape machine code $c$ and a binary string $\alpha$, converting the associated $k$-tape machine at $\alpha$ gives the same finite machine as converting the machine decoded from $\alpha$.

**Proof.** Both conversions produce a finite machine with two work tapes, state space indexed by the decoded machine’s state count, and underlying transition machine equal to that decoded machine. These fields agree by unfolding the definitions, so the resulting structures are definitionally equal.
