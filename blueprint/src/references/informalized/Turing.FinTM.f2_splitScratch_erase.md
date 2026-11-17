<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitScratch_erase -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Erasing the First Scratch Cell

**Claim.** For natural numbers $q$ and $j$, let the Boolean-valued partial tape be true exactly at integer positions $z$ with $j\le z<q$. Updating this tape at $j$ to blank gives the tape that is true exactly where $j+1\le z<q$.

**Proof.** To show the two partial tapes are equal, compare their values at an arbitrary integer position $z$. If $z=j$, the update makes the value blank, and the tape starting at $j+1$ is also blank there. If $z\ne j$, the update leaves the original value unchanged. In this case, the condition $j\le z<q$ is equivalent to $j+1\le z<q$: since $z$ and $j$ are integers and $z\ne j$, the first inequality forces $z\ge j+1$. Thus both tapes have the same value at every position, so they are equal.
