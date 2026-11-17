<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMWidthExample.lean :: Complexity.LogProg.WidthExample.enum_loop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Enumeration Loop Halting

**Claim.** For any language $P$, input word $x$, and natural number $n$ with $2^n\le B$, let $k,u$ satisfy $u+k=2^n$. For either Boolean value $b$ such that $b$ is true exactly when there exists $w$ with $u\le w<2^n$ and the encoded pair of $x$ and the binary representation of $w$ belongs to $P$, the search program with oracle determined by $P$ halts with answer $b$, while satisfying the program precondition and keeping every register at most $B$ at every earlier step.

**Proof.** Induct on the remaining count $k$. At every configuration before the halt, the register guard (`guard_rf`) supplies the precondition and the bound $B$.

If $k=0$, then $u=2^n$, so there is no integer in the interval $[u,2^n)$. The program's comparison at $\mathrm{enum}$ therefore takes the rejecting branch and halts with answer false, exactly the Boolean value specified by the equivalence.

For $k+1$, we have $u<2^n$. The program proceeds from $\mathrm{enum}$ to its oracle call on the encoded pair of $x$ and the binary representation of $u$. The oracle's indicator agrees with membership in $P$ (`indicator_eq_decide`), and the one-argument whole-input encoding is precisely this encoded pair (`vword_whole₁`). If that pair belongs to $P$, the program accepts immediately; the stated equivalence forces $b$ to be true. Otherwise it moves to the next location, increments $u$, and continues with remaining count $k$. The existence condition for the interval $[u,2^n)$ is equivalent, in this nonmembership case, to the same condition for $[u+1,2^n)$: the excluded endpoint $u$ is not in $P$, so any witness must be larger. The induction hypothesis gives the required halt and answer.

**Key facts.** `Complexity.LogProg.AHalt.step`, `Complexity.LogProg.WidthExample.guard_rf`, `Complexity.LogProg.WidthExample.rf_1`, `Complexity.LogProg.WidthExample.rf_3`, `Complexity.LogProg.indicator_eq_decide`, `Complexity.LogProg.vword_whole₁`, `Complexity.LogProg.AHalt.ret`, `Complexity.LogProg.WidthExample.rf_upd3`.
