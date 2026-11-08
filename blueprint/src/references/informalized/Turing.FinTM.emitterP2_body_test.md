<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_body_test -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Controller Testing Segment

**Claim.** From the completed-preparation configuration, the controller reaches the first erasure phase with verdict determined by whether $u=v$, preserving the bank words, within the stated time bound and without visiting the anchor.

**Proof.** Starting at preparation state $8$ with the flag false, one control transition enters the width-start phase. The width-call result simulates $C$ for $a$ steps, reaching width state $c_x$ with $u$ on the width bank and preserving the other words; its safety conclusion excludes the anchor throughout. A further control transition enters length-start. The length-call result similarly simulates $D$ for $b$ steps, reaching length state $d_x$ with $v$ on the length bank and preserving the other words, again with anchor avoidance. The endpoint transitions then enter the comparison phase.

The comparison result compares the two bank words and reaches comparison state $2$ with its Boolean register equal to the truth value of $u=v$, without changing those words. A final control transition enters the first erasure phase carrying that verdict. The runs are concatenated using the safety-joining lemma; the individual control transitions preserve safety by the one-step transition lemma. Adding their durations to $a+b$ and the comparison bound gives $a+b+2(\max(|u|,|v|+1))+4$, equivalently the stated bound $a+b+2(\max(|u|,|v|)+1)+4$.

**Key facts.** `Turing.FinTM.emitterP2_after`, `Turing.FinTM.emitterP2_body_width`, `Turing.FinTM.splitSafe_join`, `Turing.FinTM.emitterP2_body_length`, `Turing.FinTM.emitterP2_body_compare`.

**Caveat.** The supplied upstream entries for the width and length call lemmas are truncated, so their exact endpoint and safety guarantees are inferred from the target statement and proof-source use. The comparison lemma's stated time bound supports the claimed estimate.
