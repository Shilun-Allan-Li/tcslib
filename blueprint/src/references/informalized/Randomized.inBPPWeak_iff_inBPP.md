<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Classes.lean :: Randomized.inBPPWeak_iff_inBPP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weak and Standard BPP Coincide

**Claim.** For a verifier model closed under majority repetition, a language has a polynomial-time verifier with the specified inverse-polynomial advantage over random guessing if and only if it has a polynomial-time verifier with acceptance probability at least $2/3$ on members and rejection probability at least $2/3$ on nonmembers.

**Proof.** For the forward implication, start with a weak verifier and apply the error-reduction theorem to obtain a strong verifier (`Randomized.bpp_error_reduction`), then convert that strong verifier to the stated BPP form (`Randomized.InBPPStrong.toInBPP`). For the reverse implication, use the same verifier and its existing efficiency bound. The weak advantage is at most $1/6$ (`Randomized.weakAdv_le_sixth`), so $1/2$ plus that advantage is at most $2/3$. Therefore the strong verifier's $2/3$ success guarantee implies the required weak guarantee on both members and nonmembers.

**Key facts.** `Randomized.bpp_error_reduction`, `Randomized.InBPPStrong.toInBPP`, `Randomized.weakAdv_le_sixth`.
