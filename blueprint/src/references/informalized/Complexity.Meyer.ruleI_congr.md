<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerSoundInput.lean :: Complexity.Meyer.ruleI_congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input-Rule Congruence

**Claim.** If two tape-content functions agree at every integer, then evaluating the input-head update rule with either function gives the same result.

**Proof.** The pointwise hypothesis says $f(e)=g(e)$ for every integer $e$, hence the functions are equal by function extensionality. Substituting this equality into the definition of the input-head update rule makes the two evaluations identical, including the conditional test and the selected tape value.
