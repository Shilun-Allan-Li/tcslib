<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.composeThreeQueryVerifier_distribution -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composed Verifier Seed Distribution

**Claim.** The composed verifier samples a verifier seed according to the original distribution and then samples a clause index according to the reduction's clause distribution, returning the resulting pair.

**Proof.** By definition, the composed verifier's seed distribution is the bind of the original verifier distribution with the clause distribution mapped to pairs. The named composed seed is exactly the pair consisting of the sampled verifier seed and clause index. Unfolding this pair definition leaves both distributions unchanged, so the two sides are definitionally equal.
