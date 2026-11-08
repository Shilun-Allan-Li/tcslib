<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Sequence.lean :: BooleanAnalysis.GaussianSpace.Invariance.hybridInput_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial hybrid identity

**Claim.** At hybrid parameter $r=0$, every coordinate of the hybrid family is taken from the left family.

**Proof.** Fix a coordinate $i$. Since $i$ has a nonnegative index, it cannot satisfy $i<0$. Thus the definition of the hybrid index selects the left copy, and the hybrid input at $0$ agrees with the left family at every coordinate. Hence the two functions are equal.
