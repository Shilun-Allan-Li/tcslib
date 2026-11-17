<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean :: Turing.FinTM.foldMove_correct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of the translated head move

**Claim.** Translating a move using the current side and origin flag produces a folded-coordinate displacement that reaches the folded coordinate of the moved original head, and records the correct new side.

**Proof.** Split first according to whether $z$ is nonnegative, and then according to the three possible move directions. If $z\ge 0$, its folded coordinate is $z$ and its side is the nonnegative side; a positive move advances the folded coordinate, a zero move leaves it fixed, and a negative move either crosses the origin (when $z=0$) or moves one step toward it. If $z<0$, the folded coordinate is $-z-1$ and the side is negative; a negative move advances the folded coordinate, while a positive move either crosses the origin when the folded coordinate is zero or moves one step toward it. In each case, the displacement specified by the translation rule makes the new folded coordinate equal to the fold of $z+d$, and the output side is exactly whether $z+d$ is nonnegative.
