<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PolyTimeModel.lean :: Randomized.polyTimeModel_closedUnderAnswerIs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closure Under Fixed Answers

**Claim.** For every verifier $M$ and Boolean value $b$, if $M$ is efficient in the polynomial-time verifier model, then the verifier that accepts $(x,r)$ exactly when $M(x,r)=b$ is also efficient in that model.

**Proof.** Choose the polynomial-time language witnessing that $M$ returns the answer $b$ as the new verifier's true-language. Take its complement as the new false-language; the complement remains in polynomial time (Complexity.compl_mem_P). For each input pair, the original verifier's witness equivalence identifies membership in the chosen language with the statement that $M$ returns $b$. Thus the new verifier returns true exactly on that language. It returns false exactly when $M$ does not return $b$, which is membership in the complementary language. This holds for either Boolean value $b$, establishing efficiency in the model.

**Key facts.** `Complexity.compl_mem_P`.
