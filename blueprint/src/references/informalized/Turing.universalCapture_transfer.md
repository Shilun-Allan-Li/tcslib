<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalStartup.lean :: Turing.universalCapture_transfer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transfer to the Interpreter

**Claim.** If the original configuration is halted, one step of the capture wrapper from its first-phase configuration is the interpreter-entry configuration associated to it.

**Proof.** Since the original state is `none`, the wrapper's first-phase state is the tagged halted state. Its transition is the control action that moves to the interpreter's initial state, with zero input-head movement and no work-tape writes or head movements. Consequently the input position, all tapes, and all work-tape heads are preserved, while the state changes to interpreter entry and the external output remains empty. The zero-move identity for input positions (`Turing.moveInputPos_zero`) supplies the input-position component; the other components agree directly with the definitions.

**Key facts.** `Turing.moveInputPos_zero`.
