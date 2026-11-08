<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_clean_exit_words -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clean Exit at a Prepared Seam

**Claim.** The administrative configuration based on the seam with $s$ on tape zero, retained word $y$, control $q'$, input head at position $1$, capture head at position $0$, and empty output is the two-ended configuration with control $q'$, tape zero containing $s$, the last tape containing $y$, both endpoint heads at position $0$, and empty output.

**Proof.** Expand the administrative configuration. Its original tape block comes from the logged initial word configuration with empty history, which by the logged-word identity (`enumCont_log_words`) is the ordinary word configuration on the enlarged block of tapes. The added capture tape contains the retained word $y$. The identity extending a word configuration with an endpoint (`enumCont_extend_words`) says that the first tape contains $s$, the last contains $y$, and every tape between them is blank. The input position and control are the stipulated ones, and the definition of the two-ended configuration assigns head position zero to both endpoints and empty output. The work-head positions in the administrative configuration agree with these values, so the configurations agree in every field.

**Key facts.** `Complexity.enumCont_log_words`, `Complexity.enumCont_extend_words`.
