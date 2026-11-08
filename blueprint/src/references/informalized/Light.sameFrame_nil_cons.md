<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Frames.lean :: Light.sameFrame_nil_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty frame versus a cons frame

**Claim.** For an integer $b$ and a list $m$ of integers, the zero-padded frames of the empty list and $b::m$ are equal if and only if $b=0$ and the zero-padded frames of the empty list and $m$ are equal.

**Proof.** Suppose first that the two frames agree. Evaluating at index $0$, the empty frame gives $0$ and the frame of $b::m$ gives $b$, so $b=0$. At each index $i+1$, the frame of $b::m$ reads the entry of $m$ at index $i$ (with zero padding), so agreement there says exactly that the frames of the empty list and $m$ agree at $i$. Conversely, assume $b=0$ and those latter frames agree. At index $0$, both frames have value $0=b$. At every successor index $i+1$, their values agree by the assumed equality of the frames of the empty list and $m$. Hence the original frames agree at every index.
