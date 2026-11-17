<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Inclusions.lean :: Randomized.mem_EXP_of_inBPP_polyTimeModel -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# BPP Is Contained in EXP

**Claim.** Every language recognized by the polynomial-time verifier model belongs to $\mathrm{EXP}$.

**Proof.** The polynomial-time Sipser–Gács characterization `Randomized.sipser_gacs_polyTime` places any language in this verifier model in $\Sigma_2^P$ (and also in $\Pi_2^P$). Apply the containment $\Sigma_2^P\subseteq\mathrm{EXP}$ (`Complexity.SigmaP_two_subset_EXP`) to the first of these conclusions to obtain membership in $\mathrm{EXP}$.

**Key facts.** `Randomized.sipser_gacs_polyTime`, `Complexity.SigmaP_two_subset_EXP`.
