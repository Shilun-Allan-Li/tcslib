<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean :: Turing.universalStateWindow_erase -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Erasing the Next Unary Cell

**Claim.** For all natural numbers $j$ and $n$, updating the state window with $j$ consumed symbols and $n+1$ remaining symbols by writing a blank in cell $j+1$ gives the state window with $j+1$ consumed symbols and $n$ remaining symbols.

**Proof.** Compare the two functions at an arbitrary integer cell $z$. If $z=j+1$, the update makes the left side blank. At this cell the right side is also blank, since it lies at the consumed boundary for the updated window. If $z\ne j+1$, the update leaves the original value unchanged. The two windows agree there: cell $0$ is blank in both; at any other cell, membership in the interval of cells marked true changes from $j<z\le j+n+1$ to $j+1<z\le j+n+1$, which differs only at $z=j+1$. Outside that interval both values are absent. Thus the functions agree at every cell.
