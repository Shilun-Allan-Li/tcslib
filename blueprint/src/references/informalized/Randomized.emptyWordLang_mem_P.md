<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPPEqP.lean :: Randomized.emptyWordLang_mem_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The empty-word language is in polynomial time

**Claim.** The language consisting exactly of the empty binary string belongs to the class of polynomial-time decidable binary languages.

**Proof.** By the characterization of polynomial time in terms of polynomial-time computable Boolean indicators (`mem_P_iff_polyTimeComputable`), it suffices to identify the language’s indicator with the computable test that returns true exactly on the empty string. The constant-time empty-string test is polynomial-time computable (`polyTimeComputable_isNil`). For any input string, if it is empty then membership in `emptyWordLang` holds and its indicator is true; if it is nonempty, membership fails and the indicator is false. Thus the two indicator functions agree, proving the claim.

**Key facts.** `Complexity.mem_P_iff_polyTimeComputable`, `Complexity.polyTimeComputable_isNil`.
