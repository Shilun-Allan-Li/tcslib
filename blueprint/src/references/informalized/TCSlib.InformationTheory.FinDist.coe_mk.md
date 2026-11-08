<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/InformationTheory/FinDist.lean :: TCSlib.InformationTheory.FinDist.coe_mk -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a constructed distribution

**Claim.** If a function on a finite set is nonnegative at every outcome and its total sum is one, then the distribution constructed from it assigns each outcome the original function's value.

**Proof.** The constructed distribution stores the given function as its probability function. Evaluating that function at any outcome therefore returns exactly the given value.
