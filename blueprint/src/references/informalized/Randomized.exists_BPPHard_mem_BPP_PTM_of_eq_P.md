<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPPEqP.lean :: Randomized.exists_BPPHard_mem_BPP_PTM_of_eq_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A BPP-Complete Language Under Equality

**Claim.** If BPP	ext_ P equals P, then some language in BPP	ext_ P is polynomial-time many-one hard for every language in BPP	ext_ P.

**Proof.** Take the empty-word language. It belongs to P by the fact that it is decidable in deterministic polynomial time (`Randomized.emptyWordLang_mem_P`). The assumed equality therefore places it in BPP_PTM. For any language L' in BPP_PTM, the same equality puts L' in P, and every P language is polynomial-time many-one reducible to the empty-word language (`Randomized.polyTimeReducible_emptyWordLang`). Thus the empty-word language is the required member and is hard for the whole class.

**Key facts.** `Randomized.emptyWordLang_mem_P`, `Randomized.polyTimeReducible_emptyWordLang`.
