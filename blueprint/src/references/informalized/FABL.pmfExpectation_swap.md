<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLTFNoiseCorrection.lean :: FABL.pmfExpectation_swap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Interchanging Two Finite Expectations

**Claim.** For a function on the product of a finite probability space with itself, the two iterated expectations agree when the order of averaging is reversed.

**Proof.** Expand both iterated expectations into finite sums. Distribute the outer probability weight across the inner sum in each expression. Interchanging the order of the two finite sums identifies their terms: each is the product of the two point weights and the same value $H(x,y)$. Thus the iterated expectations agree.
