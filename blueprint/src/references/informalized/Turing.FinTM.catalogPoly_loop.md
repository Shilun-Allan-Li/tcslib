<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.catalogPoly_loop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Main Loop Invariant

**Claim.** Under the stated head-position and counter hypotheses, the machine’s run from loop level $i$ reaches advance state $i+1$ after the specified number of steps, restores the head positions to $h$, and appends $rCq^i$ ones to the output.

**Proof.** The proof first establishes a one-cycle statement for each level $i$: when head $i$ is at $j<q$, the loop performs $Cq^i$ emissions and returns to the same loop level with that head advanced to $j+1$. The head reads a unary mark because its position is below $q$, so the transition lowers the control level (or, at level zero, enters emission state $C$). At level zero, the emission-chain result supplies the $C$ output symbols, after which the advance transition returns to loop level zero with its head moved right. At positive level, strong induction applies the loop result at level $i-1$: the lower heads start at zero, as required by the head-position hypothesis. This inner run emits $Cq^{i-1}$ ones and returns to level $i$; the advance step then moves head $i$ right. The identity $q(Cq^{i-1})=Cq^i$ gives the asserted output per cycle. The movement and position updates follow from the one-head movement calculation (`catalogPolyMove_apply`) and the advance-step result (`catalogPoly_advance`).

Now induct on the number $r$ of remaining head positions. If $r=0$, then $j=q$: the loop detects a blank cell and enters rewind with head $i$ at $q-1$. The rewind result returns it to position zero and enters advance state $i+1$, while the hypothesis says the original position $h(i)$ was zero; hence the final positions agree with $h$ and no output is added. If $r+1>0$, then $j<q$. Apply the one-cycle statement, then the induction hypothesis with the head advanced to $j+1$ and the remaining count reduced by one. The two output blocks concatenate to $r+1$ copies of the per-cycle block, yielding $(r+1)Cq^i$ ones. The run-length identities follow from decomposing a run into consecutive segments (`runFrom_add`, `runFrom_succ_eq_step`, `runFrom_zero`) and the recursive definition of the cost.

**Key facts.** `Turing.FinTM.catalogPolyMove_apply`, `Turing.FinTM.catalogPoly_advance`, `Turing.FinTM.catalogPoly_emit`, `Turing.FinTM.catalogPoly_rewind`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
