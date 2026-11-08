<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_body_compare -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Comparison of installed words

**Claim.** The controller compares the installed words $u$ and $v$, reaches the comparison result state with their equality bit, preserves all installed words, and avoids the anchor within the stated bound.

**Proof.** The auxiliary comparison machine scans the two words in parallel, retaining a Boolean flag that records whether every pair of symbols seen so far agrees. Once both scans reach the ends, it enters state $2$ with the flag equal to the truth value of $u=v$. This run takes at most $2(\max(|u|,|v|)+1)$ steps and avoids the auxiliary terminal state beforehand (`emitter_compare_first`). Apply the phase simulation lemma to transfer this run to the controller's comparison phase; the controller agrees with the embedded comparison machine on all states before state $2$, and those states are away from the anchor (`emitterP2_phase`). The paired embedding frame lemma identifies the embedded initial and final configurations with the controller configurations carrying the original words (`emitterP2_pair_frame`). Thus the words remain installed, the result bit is correct, and the controller stays anchor-free.

**Key facts.** `Turing.FinTM.emitter_compare_first`, `Turing.FinTM.emitterP2_phase`, `Turing.FinTM.emitterP2_pair_frame`.
