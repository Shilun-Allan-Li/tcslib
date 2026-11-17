<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.nonDictatorBooleanFunctions_nonempty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Non-Dictator Boolean Function

**Claim.** For every n, there exists a Boolean function on n coordinates that is not a dictator.

**Proof.** Take the constant function with value 1. It belongs to the set of all Boolean functions. It cannot equal any dictator: at the input whose every coordinate is −1, the constant function has value 1, while every coordinate dictator has value −1. Thus this function is not a dictator, proving the set in question is nonempty.
