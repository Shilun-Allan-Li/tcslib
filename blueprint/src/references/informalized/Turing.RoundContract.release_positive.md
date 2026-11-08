<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean :: Turing.RoundContract.release_positive -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive duration after releasing rounds

**Claim.** The contract obtained by releasing a round contract has strictly positive running time for every anchor-state configuration satisfying its precondition.

**Proof.** Fix a parameter and a configuration satisfying the released contract’s entry-state and precondition hypotheses. By the definition of the released contract, its entry-state condition translates to the original configuration being in the anchor state. Apply the original round contract’s positivity property to this configuration and precondition. The resulting strict positivity is exactly the released contract’s running-time claim.
