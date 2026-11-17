<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMKit.lean :: Complexity.LogProg.nsem_guess -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nondeterministic Interval Guess

**Claim.** The guessing loop terminates within the register bound and accepts exactly when some $j$ in the half-open interval $[v(g),v(nr))$ satisfies $Q(j)$.

**Proof.** Induct on the interval length $k=v(nr)-v(g)$. If $k=0$, the test immediately finds $g=nr$ and enters the rejecting halt state. Its semantics follow from the false-return rule (`NSem.ret`) and the equality branch rule (`NSem.jeq_pos`); the interval is empty, so the existential claim is false. If $k>0$, the test takes the unequal branch to the choice state. Choosing the exit state tests $Q(v(g))$, which is covered by the assumed exit semantics at the left endpoint. Choosing to continue increments $g$ and returns to the test. This increment remains within the bound because the new value is at most $v(nr)\le B$; the register-update bound lemma (`register_update_le`) supplies the guard for the updated assignment. The gap has decreased by one, so induction gives the semantics for the remaining interval. The choice rule (`NSem.choose`) combines acceptance from either the current endpoint or the remaining interval, and the unequal-test and increment rules (`NSem.jeq_neg`, `NSem.inc`) restore the loop's first step. Finally, these two possibilities are equivalent to existence in the original interval: either the witness is its left endpoint, or it lies in the remaining interval. The semantics congruence rule (`NSem.congr`) expresses this equivalence in the claimed predicate.

**Key facts.** `Complexity.LogProg.NSem.ret`, `Complexity.LogProg.NSem.jeq_pos`, `Complexity.LogProg.register_update_le`, `Complexity.LogProg.NSem.choose`, `Complexity.LogProg.NSem.jeq_neg`, `Complexity.LogProg.NSem.inc`, `Complexity.LogProg.NSem.congr`.
