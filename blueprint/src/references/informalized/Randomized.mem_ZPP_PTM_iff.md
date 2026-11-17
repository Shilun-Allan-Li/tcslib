<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZPPHostsClasses.lean :: Randomized.mem_ZPP_PTM_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# ZPP Verifier Characterization

**Claim.** A language belongs to polynomial-time ZPP exactly when it has an efficient verifier with polynomially many random bits, no incorrect Boolean outputs, and nonhalting probability at most $1/2$ on every input.

**Proof.** The class equality `ZPP_PTM_eq_setOf_inZPP` identifies polynomial-time ZPP with the set of languages satisfying the definition `InZPP polyTimeModel`. Unfolding membership in that set gives the verifier characterization directly, including efficiency, the two one-sided correctness conditions, and the bound on nonhalting probability.

**Key facts.** `Randomized.ZPP_PTM_eq_setOf_inZPP`.
