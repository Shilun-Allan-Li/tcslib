<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satStreamInv_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Startup invariant

**Claim.** For every finite binary string $x$, the encoded startup state is the canonical encoding of a state whose consumed length is at most $|x|$ and whose fresh-variable cursor is at most $|x|$ plus its consumed length.

**Proof.** Choose the startup state itself as the state witnessing the existential invariant. Its encoding is therefore the specified startup word by definition. The startup bound lemma supplies both required inequalities for this state, completing the invariant.

**Key facts.** `Complexity.satStreamStart_bound`.
