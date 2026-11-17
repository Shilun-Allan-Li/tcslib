<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CertShell.lean :: Turing.cert_bank_word -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Word on an Embedded Tape

**Claim.** Replacing the contents of the embedded tape corresponding to index zero by $w$ makes the embedded assignment agree with the standard assignment: it has $w$ at index zero and the empty word at every other index.

**Proof.** Fix an embedded index $i$. If $i=0$, the update replaces the frame’s empty word at that slot by $w$, so the result is the standard assignment’s value there. If $i\ne0$, injectivity ensures that the embedded slot for $i$ differs from the updated slot. The update therefore leaves the frame value unchanged, and the frame hypothesis says that value is empty. Since $i$ is nonzero, this is also its value in the standard assignment.
