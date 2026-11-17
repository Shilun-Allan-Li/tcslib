<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/CNFEncoding.lean :: Std.Sat.CNF.takeTrues_repr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reconstructing a Boolean string

**Claim.** For every finite Boolean string $x$, removing its longest initial run of $1$s gives a pair $(k,y)$ such that $1^k y=x$.

**Proof.** Induct on the string. The empty string is reconstructed immediately. For a cons cell, if its first bit is false, the split has length zero and leaves the string unchanged. If its first bit is true, apply the induction hypothesis to the tail: that tail is a run of $1$s followed by its remainder. Putting the initial true bit back increases the run length by one, so the reconstructed string is the original one.
