<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satDrop_double -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counting a Doubled Bit

**Claim.** If the input has the form $x=p\mathbin{++}[b,b]\mathbin{++}r$, then starting in state $0$ at the clamped offset $|p|$, with a unary counter of length $n$ headed at $n$ and empty output, the suffix-extraction machine reaches after two steps state $0$ at the clamped offset $|p|+2$, with a unary counter of length $n+1$ headed at $n+1$ and empty output.

**Proof.** First, the input head at the clamped offset $|p|$ reads the first copy of $b$, since $x[|p|]=b$ by the assumed decomposition. The transition from state $0$ therefore moves the input head right, leaves the counter and output unchanged, and enters state $1$ if $b$ is true or state $2$ if $b$ is false. The clamped-position successor law identifies the new offset as $|p|+1$, and the silent-move configuration law records this transition (`satDrop_move`). At that offset the head reads the second copy of $b$, again by the decomposition of $x$. In either resulting state, the machine's transition writes a true bit at the counter head and moves both heads right, entering state $0$. The unary-counter write law gives counter length and head position $n+1$, while the clamped-position successor law gives input offset $|p|+2$; the corresponding configuration law identifies all fields (`satDrop_write`). Thus the two successive transitions yield the asserted configuration.

**Key facts.** `Complexity.satDrop_move`, `Complexity.satDrop_write`, `Complexity.satStreamPos_read`, `Complexity.satStreamPos_succ`.
