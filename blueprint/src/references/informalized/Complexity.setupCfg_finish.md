<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.setupCfg_finish -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completion of the Macrostep Schedule

**Claim.** Starting in macrostep-check phase with the specified unary tape, guide, and head positions, after $B(6(3B)+8)+1$ steps the machine is halted with unary head at $B+1$, and the other specified setup data are as claimed.

**Proof.** Apply the macrostep completion result with radius $R=3B$ to the given setup configuration. Its hypotheses require that the guide tape is the guide of radius $R$, that each unary cell at positions $j+1$ for $j<B$ contains a unit marker, and that position $B+1$ is blank. The definition of the setup configuration identifies its guide and unary tapes with the stated tapes; `unaryTape_unit` supplies the marker condition and `unaryTape_end` supplies the blank endpoint. The result gives the halted configuration after $B(6R+8)+1$ steps. Rewriting the abstract macrostep configuration back into setup form by `macroCfg_setup` gives the asserted configuration, and substituting $R=3B$ yields the stated time.

**Key facts.** `Complexity.macroCfg_finish`, `Complexity.unaryTape_unit`, `Complexity.unaryTape_end`, `Complexity.macroCfg_setup`.
