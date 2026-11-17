<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.copyGuide_next -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Extending the Partial Copy Guide

**Claim.** For every natural number $j$, updating the partial copy guide at coordinate $j$ with the origin mark if $j=0$ and the interior mark otherwise yields the partial copy guide for $j+1$ copied input cells.

**Proof.** Compare the two functions at an arbitrary integer coordinate $z$. If $z=j$, the update assigns the prescribed mark. Since a natural number viewed as an integer cannot equal $-1$, the definition of the guide for $j+1$ gives that same mark there: at $j=0$ it is the origin mark, and otherwise it is the interior mark. If $z\ne j$, the update leaves the old guide unchanged. At this coordinate, the interval conditions $0\le z<j$ and $0\le z<j+1$ are equivalent: there is no integer strictly between $j$ and $j+1$. Thus the old and new guide definitions agree, including their special case at $z=-1$. The functions agree at every coordinate, so they are equal.
