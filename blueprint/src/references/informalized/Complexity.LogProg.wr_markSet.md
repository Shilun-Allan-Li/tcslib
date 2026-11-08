<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Clean.lean :: Complexity.LogProg.wr_markSet -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Writing the Marked Set

**Claim.** Starting from the partial marking that is true at $0$, false on $F$, and undefined elsewhere, the specified write operation at $p$ yields the marking that is true at $0$, false on $F\cup\{p\}$, and undefined elsewhere.

**Proof.** Compare the two partial functions at an arbitrary integer $z$. If $p=0$, the current marking at $p$ is true, so the instruction leaves it unchanged; inserting $0$ into $F$ does not change the marking, since the special rule at zero still assigns true there. If $p\ne0$, the marking at $p$ is not true: it is either already false or undefined. The operation therefore writes false at $p$. At every $z\ne p$, the update leaves the value unchanged, and membership in $F\cup\{p\}$ agrees with membership in $F$ there. At $p$, the new value is false, as required. Thus the functions agree at every integer.
