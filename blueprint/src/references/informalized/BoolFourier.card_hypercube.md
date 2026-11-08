<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/BoolFourier.lean :: BoolFourier.card_hypercube -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cardinality of the Boolean hypercube

**Claim.** For every natural number $n$, the Boolean hypercube $\{0,1\}^n$ has exactly $2^n$ elements.

**Proof.** The hypercube consists of functions from an $n$-element coordinate set to the two-element Boolean set. The cardinality formula for a finite function space gives $2^n$: each of the $n$ coordinates has two independent choices.
