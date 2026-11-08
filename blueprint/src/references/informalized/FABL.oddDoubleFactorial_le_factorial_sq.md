<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.oddDoubleFactorial_le_factorial_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd Double Factorial Bound

**Claim.** For every natural number $m$, the odd double factorial $(2m-1)!!$ is at most $(m!)^2$.

**Proof.** Proceed by induction on $m$. The case $m=0$ is immediate. In the successor case, the first small value is also immediate, so consider $m+2$. The recurrence for the odd double factorial gives $(2m+3)!!=(2m+3)(2m+1)!!$, while the factorial recurrence gives $((m+2)!)^2=((m+2)^2)((m+1)!)^2$. The induction hypothesis bounds $(2m+1)!!$ by $((m+1)!)^2$. Also $2m+3\le(m+2)^2$, since their difference is $m^2+2m+1\ge0$. Multiplying these nonnegative bounds proves the desired inequality at $m+2$.
