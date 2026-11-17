<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean :: Turing.Contract.inPhase_positive -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of a Phase Contract

**Claim.** If the phase contract has strictly positive duration on every entry configuration satisfying its precondition, then the contract obtained by placing it inside phase $p$ of the host machine also has strictly positive duration.

**Proof.** Fix a parameter and a host configuration satisfying the new contract’s entry and precondition conditions. By definition, the new duration is the original duration on the projected configuration plus one. The original duration is a natural number, so its successor is strictly positive.
