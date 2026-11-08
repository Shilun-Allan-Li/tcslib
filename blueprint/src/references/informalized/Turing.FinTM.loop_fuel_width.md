<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loop_fuel_width -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Output Length and Running Time

**Claim.** If F outputs the binary digits of R(|y|) on every input y within T(|y|) steps, then the length of the binary digit word of R(|x|) is at most T(|x|).

**Proof.** Apply the assumed running-time computation to input x. Its output is the binary digit word of R(|x|), and the general output-length bound says that after T(|x|) steps a machine's output has length at most T(|x|) (`output_length_le`). Substituting the specified output gives the claimed inequality.

**Key facts.** `Turing.MultiTapeTM.output_length_le`.
