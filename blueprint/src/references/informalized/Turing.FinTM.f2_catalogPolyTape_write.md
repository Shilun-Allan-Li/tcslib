<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_catalogPolyTape_write -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Extending the Marked Tape Interval

**Claim.** Writing true at cell $q$ of the tape marked true exactly on integer cells $z$ with $0\le z<q$ produces the tape marked true exactly on cells $z$ with $0\le z<q+1$.

**Proof.** Compare the tapes at an arbitrary integer cell $z$. If $z=q$, the update writes true there, and this cell satisfies $0\le z<q+1$. If $z\ne q$, the update leaves the cell unchanged. For such a $z$, the conditions $0\le z<q$ and $0\le z<q+1$ are equivalent: the only integer newly included when the upper endpoint increases from $q$ to $q+1$ is $q$ itself. Thus the old tape value agrees with the new interval description at every other cell as well, proving equality of the tapes.
