<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerSoundInput.lean :: Complexity.Meyer.RI_far -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Far Input Positions Are Blank

**Claim.** If the absolute value of the offset exceeds the input length plus one, then the input symbol seen at that offset is absent.

**Proof.** Write $p$ for the shifted input-head position. Since it is a valid configuration position, $0\le p\le |x|+1$. The extended lookup at $p+d$ is absent precisely when $p+d<1$ or $|x|<p+d$ (the characterization of absent extended lookups, `xhat_eq_none`). If $d$ is positive, the hypothesis $|d|>|x|+1$ gives $d>|x|+1$, so $p+d>|x|$; if $d$ is negative, it gives $d<-(|x|+1)$, so $p+d<1$. Thus in either case the lookup is absent. By the definition of the input read at offset $d$, this proves the claim.

**Key facts.** `Complexity.Meyer.xhat_eq_none`.
