<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Sequence.lean :: BooleanAnalysis.GaussianSpace.Invariance.hybridInput_all -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Final hybrid equals the right family

**Claim.** At stage $n$, the hybrid input assigns to each coordinate $i$ the function indexed by the right copy of $i$.

**Proof.** Fix a coordinate $i\in\mathrm{Fin}(n)$. Its value is less than $n$, so at stage $n$ the hybrid index selects the right summand and returns the right copy of $i$. Thus the hybrid input agrees pointwise with the stated right-family input, and the functions are equal.
