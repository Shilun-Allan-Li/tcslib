<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.taut_certificate_equiv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Certificate Characterization of Non-Tautologies

**Claim.** A binary string is outside the language of tautologies exactly when there is a binary word of length one greater than the string such that the decoded DNF evaluates to false on the assignment read from that word, with missing bits interpreted as false.

**Proof.** First, being outside the tautology language is equivalent to the existence of an assignment under which the decoded DNF evaluates to false: negate the universal condition that it evaluates to true for every assignment. Given such an assignment $a$, form a word $u$ whose entries are $a(0),a(1),\ldots,a(|x|)$. This word has length $|x|+1$. The decoded formula uses only variables with indices at most $|x|$: the number of variables in the decoded CNF is at most $|x|$ (the bound on decoded variable count, `Std.Sat.CNF.numVars_decode_le`), and the DNF is decoded from that CNF. Thus, for every variable used in the DNF, the assignment read from $u$ agrees with $a$. Evaluation depends only on those used variables (`Complexity.taut_eval_congr`), so the DNF still evaluates to false. Conversely, any word $u$ certifying false evaluation gives an assignment, namely the assignment that reads from $u$ and defaults to false beyond its length. That assignment witnesses that the decoded DNF is not true under every assignment. The specified word length is part of the certificate, while this reverse implication only needs its induced assignment.

**Key facts.** `Complexity.taut_eval_congr`, `Std.Sat.CNF.numVars_decode_le`.
