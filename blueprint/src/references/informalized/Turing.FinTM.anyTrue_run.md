<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.anyTrue_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run of the marker-existence scanner

**Claim.** For Boolean words $x$ and $r$, and any prefix $p$ with $x=pr$, the scanner started with its input head just after $p$ and empty output halts within $|r|+1$ steps, outputting the one-bit word that is true exactly when $r$ contains a true bit.

**Proof.** Proceed by induction on the remainder $r$, with the prefix allowed to vary so that the concatenation remains $x$. If $r$ is empty, the scanner takes one step from the indicated configuration and halts without emitting a marker; this is the one-bit result $[r.any\ id]$ for the empty word. If $r=b::r'$, split on the first bit. When $b$ is true, one transition detects it, halts, and emits the true bit, which is the result for the whole remainder. When $b$ is false, the scanner's rightward transition advances past that bit without changing the output (`scanStep_right`). Apply the induction hypothesis to the shortened remainder $r'$ with the enlarged prefix $p++[false]$; the equation $x=p++(false::r')$ supplies its required decomposition. Prepending the initial transition to that run adds one step, so its total is at most $|r'|+2=|r|+1$. Since the skipped bit is false, $r.any\ id=r'.any\ id$, and the resulting halt and output are exactly the required ones.

**Key facts.** `Turing.FinTM.scanCfg_read`, `Turing.FinTM.scanStep_right`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
