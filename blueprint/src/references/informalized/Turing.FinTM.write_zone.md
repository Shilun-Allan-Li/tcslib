<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.write_zone -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Backward Sweep Across a Tape Zone

**Claim.** A backward sweep through the reversed zone of $n$ tape blocks, initialized with head flags at coordinate $j+n$, ends with the flags at $j$ and the reversed zone of unread blocks for the action-updated configuration.

**Proof.** Proceed by induction on the zone length $n$, with the starting coordinate $j$ arbitrary. For length zero, the zone and its reverse are empty, so the sweep leaves the initial flags unchanged and produces the empty zone. For length $n+1$, the zone is the row at $j$ followed by the length-$n$ zone beginning at $j+1$. Reversing this concatenation puts the length-$n$ part first and the row at $j$ last. The sweep-fold concatenation law (`sweepFold_append`) therefore applies the sweep across those two parts in that order. The induction hypothesis processes the length-$n$ portion, carrying the flags from $j+n+1$ back to $j+1$ and producing its updated reversed zone. The one-row result (`write_row`) then processes coordinate $j$, carrying the flags from $j+1$ back to $j$ and replacing that row by its updated unread encoding. Together these are exactly the reversed updated zone of length $n+1$.

**Key facts.** `Turing.FinTM.sweepFold_append`, `Turing.FinTM.write_row`.
