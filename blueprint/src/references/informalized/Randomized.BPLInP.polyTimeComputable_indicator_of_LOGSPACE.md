<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInPWords.lean :: Randomized.BPLInP.polyTimeComputable_indicator_of_LOGSPACE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logspace Indicators Are Polynomial-Time

**Claim.** If a language over the binary alphabet is decidable in logarithmic space, then its one-bit membership indicator is polynomial-time computable.

**Proof.** Since logarithmic space is contained in polynomial time (\texttt{LOGSPACE\_subset\_P}), the language belongs to polynomial time. The characterization of polynomial-time languages by their indicator functions (\texttt{mem\_P\_iff\_polyTimeComputable}) then gives polynomial-time computability of the function that outputs the one-bit membership indicator.

**Key facts.** `Complexity.LOGSPACE_subset_P`, `Complexity.mem_P_iff_polyTimeComputable`.
