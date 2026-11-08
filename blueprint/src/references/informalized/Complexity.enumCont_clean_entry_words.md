<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_clean_entry_words -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clean Entry at a Prepared Seam

**Claim.** The captured logged seam configuration whose first work tape contains $s$ and whose other work tapes are blank is the two-ended administrative configuration with state $q$, tape zero containing $s$, the last tape blank, both endpoint heads at position $0$, input head at position $1$, and empty output.

**Proof.** First, the empty history contributes no log entries, so the logged configuration of the initial word configuration is exactly the ordinary word configuration on the enlarged set of tapes: the original tape block still has $s$ on tape zero and blanks elsewhere. This is the content of the empty-history case of the logged-word identity (`enumCont_log_words`). Capturing that configuration preserves its state, input position, and original tape block, while the new capture tape is blank because the prefix and output are empty. Since there is at least one original work tape, the first and last positions in the enlarged configuration are distinct. The tape contents therefore agree with the two-ended description: the first endpoint contains $s$, the last is blank, and any intervening positions are blank. The identity that extends a word configuration by one endpoint (`enumCont_extend_words`) gives precisely this tape-content description. Finally, the capture construction places all work heads at zero here, and both configurations have empty output; hence all fields agree.

**Key facts.** `Complexity.enumCont_log_words`, `Complexity.enumCont_extend_words`.
