<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PolyTimeModel.lean :: Randomized.polyTimeModel_closedUnderNot -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closure Under Complementation

**Claim.** For every Boolean predicate $M$, if the verifier that returns $M(x,r)$ is efficient in the model, then so is the verifier that returns the Boolean complement of $M(x,r)$.

**Proof.** Keep the same two polynomial-time witness languages for the new verifier, but exchange their roles: the language witnessing false answers for $M$ now witnesses true answers for its complement, and the language witnessing true answers now witnesses false answers. For each $(x,r)$, the original two equivalences state exactly that swapping the Boolean answer swaps membership in these languages. Hence both required witness equivalences hold for the complemented verifier.
