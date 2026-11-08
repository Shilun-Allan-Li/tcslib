<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Matching.lean :: Randomized.Matching.inBPP_BipartitePerfectMatching -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bipartite Matching Is in BPP

**Claim.** The language of encodings of bipartite graphs that have a perfect matching belongs to BPP under the given verifier model, with the stated two-thirds acceptance and rejection probability guarantees.

**Proof.** The proof reuses the established fact that this language is in RP, then applies the general inclusion of RP in BPP (Randomized.InRP.inBPP). The RP verifier has acceptance probability at least $2/3$ on members and rejects every random string on nonmembers. Consequently its rejection probability there is $1$, which is at least $2/3$, giving precisely the BPP guarantees.

**Key facts.** `Randomized.Matching.inRP_BipartitePerfectMatching`, `Randomized.InRP.inBPP`.
