<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CertShell.lean :: Turing.cert_capture_fields -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Captured Tape Contents and Head Position

**Claim.** If the capture tape lies outside the image of the tape embedding, then the embedded configuration stores the prefix followed by the configuration’s output on that tape, with its head at the length of that word.

**Proof.** Because the capture tape is outside the image of the injection, no local tape index maps to it. Hence the search defining its embedded slot finds no index. In the definition of the embedded configuration, the tape contents and head position therefore take the capture-tape branch: the buffer of the prefix concatenated with the output, and the length of that concatenation. This gives both asserted equalities.
