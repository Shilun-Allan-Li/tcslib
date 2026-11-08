<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ParseCmp.lean :: Complexity.LogProg.jeqPairSnd_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run of the Second-Payload Equality Test

**Claim.** On the paired input containing the unary prefix and the encoding of $u,w$, the specified routine compares $w$ with the register’s binary word, reaches the affirmative or negative state according to equality, and keeps the register head within the stated bounds before finishing.

**Proof.** Rewrite the input as $2n$ ones, a delimiter, the doubled word $u$, a delimiter, and then $w$. The routine skips the unary prefix (`Complexity.LogProg.skipPrefix_run`), then skips the encoded first payload and its delimiter to arrive at the beginning of $w$ (`Complexity.LogProg.pairSkip_run`). The ordinary comparison routine now compares the plain input word $w$ with the register word and reaches a return state recording whether they agree (`Complexity.LogProg.cmpPlain_run`). The return routine brings the heads back to their required positions and enters the affirmative state exactly when $w$ equals the register word (`Complexity.LogProg.cmpReturn`). Concatenate these stages using the run-addition identity (`Complexity.LogProg.rrun_add`); convert the first two reachability bounds to the common register-head bound and compose them (`Complexity.LogProg.Reaches.toB`, `Complexity.LogProg.ReachesB.trans`). The delimiter and segment locations follow from the pairing identity, the doubled-unary identity, and the list-indexing facts (`Turing.pairEncode_eq_dbl`, `Complexity.LogProg.dbl_replicate`, `Complexity.LogProg.getElem?_append_len`, `Complexity.LogProg.inSym_succ`).

**Key facts.** `Turing.pairEncode_eq_dbl`, `Complexity.LogProg.dbl_replicate`, `Complexity.LogProg.skipPrefix_run`, `Complexity.LogProg.pairSkip_run`, `Complexity.LogProg.cmpPlain_run`, `Complexity.LogProg.cmpReturn`, `Complexity.LogProg.Reaches.toB`, `Complexity.LogProg.ReachesB.trans`, `Complexity.LogProg.rrun_add`, `Complexity.LogProg.getElem?_append_len`, `Complexity.LogProg.inSym_succ`.
