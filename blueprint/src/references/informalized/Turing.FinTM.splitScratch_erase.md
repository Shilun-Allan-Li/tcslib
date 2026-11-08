<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitScratch_erase -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Erasing a Unary Scratch Cell

**Claim.** Blanking position $j$ on the unary scratch tape with its first $j$ cells cleared yields the tape with its first $j+1$ cells cleared.

**Proof.** Check the tape functions at each integer position $z$. At $z=j$, the update makes the value blank, as required after clearing the next cell. At every other position, the update leaves the old value unchanged. Since $z\ne j$, the condition $j\le z$ is equivalent to $j+1\le z$; the upper bound $z<q$ is unchanged. Thus the old and new tape values agree at every position, proving equality of the functions.
