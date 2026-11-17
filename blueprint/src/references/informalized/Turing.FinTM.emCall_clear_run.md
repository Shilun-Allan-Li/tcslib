<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_clear_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Cleanup of a Marked Interval

**Claim.** Under the stated endpoint, head-position, and blankness assumptions, the cleaner reaches state $3$ with all tapes blank and all heads at the origin in positive time at most $3m+4$.

**Proof.** Let $n=(\ell+m-1)$, viewed as a nonnegative integer; the hypotheses $\ell\le0<\ell+m$ ensure this is a valid natural number, and $n<m$. First run the initial leftward scan for $j$, which takes $j+2$ steps and reaches state $1$ at $\ell$ (`emCall_clear_left`). Next run the rightward erasure pass for $m$ steps. The scan formula `emCall_clear_scan` describes the resulting tapes as the original tapes with the interval $[\ell,\ell+m)$ erased. The hypothesis that the data tape is blank off that interval, together with `emCall_cleared_all`, shows that the data tape is now entirely blank; the marker tape is also blank everywhere because it was supported exactly on that interval. At the right endpoint $\ell+m$, one further transition enters state $2$ and places the heads at $n=\ell+m-1$, the last cell of the interval. The cleaner then rewinds from $n$ to the origin and erases the origin marker in $n+1$ steps (`emCall_clear_origin`). Concatenate these runs using `runFrom_add` (and the one-step form `runFrom_succ_eq_step'`). The total is $(j+2)+(m+1)+(n+1)$, which is positive and at most $3m+4$ because $j<m$ and $n<m$.

**Key facts.** `Turing.FinTM.emCall_clear_left`, `Turing.FinTM.emCall_clear_scan`, `Turing.FinTM.emCall_cleared_all`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.emCall_clear_origin`, `Turing.moveInputPos_zero`.
