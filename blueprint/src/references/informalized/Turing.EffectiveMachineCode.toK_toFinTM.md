<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalK.lean :: Turing.EffectiveMachineCode.toK_toFinTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conversion to a Finite Machine

**Claim.** Converting the $K$-machine associated to an effective machine code at a binary string gives the same finite machine as converting the machine decoded from that string.

**Proof.** Both finite machines use the same number of work tapes, the same state type, and the same underlying transition machine after unfolding the definitions of the two conversions and the associated $K$-machine. Thus the constructions reduce definitionally to the same finite machine.
