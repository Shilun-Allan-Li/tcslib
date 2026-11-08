<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean :: Turing.FinTM.arBuffer_update -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One buffer fill step

**Claim.** For an offset $j\in\{0,\ldots,N\}$, updating entry $j$ of each tape's buffer after $j$ reading steps to the corresponding coded entry produces the buffer after $j+1$ reading steps.

**Proof.** Fix a tape $i$ and position $b$. If $b=j$, the update sets the entry to $E(r(i))(j)$, and the buffer at depth $j+1$ retains exactly that coded entry. If $b\ne j$, the update leaves the old entry unchanged. In this case the conditions $b<j$ and $b<j+1$ are equivalent, since $b$ cannot equal $j$; therefore the old buffer entry agrees with the depth-$j+1$ buffer entry. Agreement at every tape and position proves the stated equality.
