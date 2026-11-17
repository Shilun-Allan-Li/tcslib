<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFTerm.blockCode_card_positions -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Block code position count

**Claim.** If the term has width at most $w$, then the block code formed from any set of its literal positions has as many positions as that set.

**Proof.** By the description of the block code's position set, its positions are the image of the chosen set under the position embedding (`FABL.DNFTerm.blockCode_positions`). The embedding is injective, so mapping a finite set along it preserves cardinality. Hence the block code has exactly as many positions as the original set.

**Key facts.** `FABL.DNFTerm.blockCode_positions`.
