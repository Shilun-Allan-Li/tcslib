<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LevelWeightAsymptotics.lean :: FABL.log_four_lt_seven_fifths -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# An Upper Bound for the Logarithm of Four

**Claim.** The natural logarithm of $4$ is less than $7/5$.

**Proof.** Use the identity $\log 4=2\log 2$. The standard bound $\log 2<9/10$ then gives $\log 4<9/5$—which is not the desired estimate, so the proof instead uses the sharper numerical bound supplied by the cited library inequality $\texttt{Real.log\_two\_lt\_d9}$ together with $\log 4=2\log 2$; these yield $\log 4<7/5$.

**Caveat.** The proof relies on the unstated numerical inequality Real.log_two_lt_d9, whose statement is not included in upstream; the exact bound cannot be confirmed from the supplied payload.
