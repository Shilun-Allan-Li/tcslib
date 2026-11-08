<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardSemantics.lean :: Complexity.TQBFHard.steps_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Addition of step counts

**Claim.** An $(k+m)$-step chain from $A$ to $B$ exists exactly when some length-$w$ string $z$ splits it into a $k$-step chain from $A$ to $z$ and an $m$-step chain from $z$ to $B$.

**Proof.** Induct on $m$. When $m=0$, the left side is a $k$-step chain, while the right side can take $z=B$: the zero-step part from $B$ to itself holds, and the given chain is the first part. Conversely, a zero-step chain from $z$ to $B$ says $z=B$, so the first chain is already the desired one. For the successor case, view a $(k+m+1)$-step chain as a $(k+m)$-step chain ending at some penultimate string $y$, followed by one $E$-edge to $B$. In the forward direction, apply the induction hypothesis to split the chain ending at $y$, yielding the required intermediate $z$, and retain the final edge. In the reverse direction, combine the $k$-step and $m$-step portions by the induction hypothesis to get a $(k+m)$-step chain from $A$ to $y$; appending the last edge gives the result. The length hypotheses ensure each chosen intermediate has length $w$.
