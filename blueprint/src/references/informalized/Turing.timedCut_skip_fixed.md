<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedCut_skip_fixed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Skipping Fixed Action Fields

**Claim.** If the field index and remaining count satisfy $field+n=7$, then after $n+1$ steps the interpreter enters unary-tail scanning, with its cursor advanced by $n+1$ and its state tape and state cursor unchanged.

**Proof.** Induct on $n$. When $n=0$, the condition forces the field to be the eighth and final fixed field. The transition rule for this case enters unary-tail scanning and moves the table cursor forward by one; the zero-run identity and the one-step run identity (`Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step`) give the claimed run. For the successor case, the current field is not the last. Its transition advances to the next fixed field and moves the table cursor forward by one without changing the state tape or its cursor. Apply the induction hypothesis at that next field, with cursor $tp+1$ and one fewer remaining step. The one-step configuration update is supplied by `timedCut_Eval_step`; the successor-run identity expresses the run as that step followed by the remaining run. The cursor arithmetic gives $(tp+1)+n+1=tp+(n+1)+1$, as required.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.timedCut_Eval_step`.
