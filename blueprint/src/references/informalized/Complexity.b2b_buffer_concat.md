<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: Complexity.b2b_buffer_concat -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concatenation of Buffered Words

**Claim.** Replacing the cells in the interval from $|x|$ through $|x|+|u|-1$ by the buffer for $u$, shifted by $|x|$, and keeping the buffer for $x$ elsewhere gives the buffer for the concatenated word $xu$.

**Proof.** Fix a tape position $z\in\mathbb Z$. If $|x|\le z$, then $z\ge0$ and the buffer for $x$ is blank at $z$. The shifted position $z-|x|$ indexes precisely the corresponding position of the appended word $u$; when it lies within $u$, the interval rule selects that symbol, and when it lies beyond $u$, both sides are blank. If $|x|>z$ and $z\ge0$, then $z<|x|$, so the position is within the $x$ portion of the concatenation, and the buffer for the concatenation agrees with that for $x$ there. If $z<0$, both buffer definitions give blank. Hence the two tape-content functions agree at every integer position, so they are equal.
