<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/IndicatorSmoothing.lean :: BooleanAnalysis.GaussianSpace.measurePreserving_middleTranspose -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exchange of middle product coordinates

**Claim.** The map $((a,b),(c,d))\mapsto((a,c),(b,d))$ preserves $(\mu\otimes\mu)\otimes(\mu\otimes\mu)$ for an s-finite measure $\mu$.

**Proof.** Regroup the four factors using the measure-preserving product associativity maps (`measurePreserving_prodAssoc`), which identify nested products without changing their measure. In the resulting arrangement, swap the two middle factors; the product-measure swap preserves their product measure. Regroup the factors back by the inverse associativity maps. The identity maps on the untouched factors preserve their measures, and composing these rearrangements gives exactly $((a,b),(c,d))\mapsto((a,c),(b,d))$. Therefore the original product measure is preserved.
