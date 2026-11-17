<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.mult_finish -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Final-position termination

**Claim.** For every bit string $x$ and register assignment $v$ bounded by $4(|x|+1)$, the multiplication program started at its final-position state halts with answer true exactly when $v(12)=v(1)$ and $v(11)=0$, and every earlier configuration satisfies the instruction side conditions and register bound.

**Proof.** The final-position instruction compares registers $12$ and $1$. If they differ, the program immediately enters the answer-false state, where the return lemma guarantees termination with false while preserving the required conditions. If they agree, it advances to the final-carry state, which tests whether register $11$ is zero. The zero case returns true and the nonzero case returns false. In either branch, the return lemma supplies termination from the answer state, and the halting-step principle lifts that run back across the preceding instruction while retaining the invariant. Thus the answer is precisely the Boolean test of the two stated equalities.

**Key facts.** `Complexity.LogProg.AHalt.step`, `Complexity.mult_preconditions`, `Complexity.mult_return`.
