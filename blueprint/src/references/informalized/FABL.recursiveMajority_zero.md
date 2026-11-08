<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/SocialChoiceFunctions/Definitions.lean :: FABL.recursiveMajority_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recursive Majority at Depth Zero

**Claim.** For every natural number $n$ and every sign vector $x$ with $n^0$ coordinates, depth-zero recursive majority is the value of $x$ at its sole coordinate.

**Proof.** By the depth-zero clause of the definition, recursive majority returns $x$ evaluated at coordinate $0$. Since $n^0=1$, this is the unique coordinate.
