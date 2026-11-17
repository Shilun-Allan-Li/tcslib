<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalK.lean :: Turing.EffectiveMachineCode.toK_machine -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Machine Decoded from a Binary String

**Claim.** For every effective machine code and binary string, the associated $K$-machine construction produces the machine decoded from that string.

**Proof.** Unfolding the definitions of the associated machine and of the effective code's decoded machine gives the same underlying transition machine. The two sides are therefore equal by definitional computation.
