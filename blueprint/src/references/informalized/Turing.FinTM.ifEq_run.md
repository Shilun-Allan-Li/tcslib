<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Composition.lean :: Turing.FinTM.ifEq_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Comparator Completion

**Claim.** Under the stated length, prefix-agreement, and input-position hypotheses, the comparator reaches a halted configuration with output $u$ when $x=w_0$ and $v$ otherwise, within $r+\max(|u|,|v|)+2$ steps.

**Proof.** Induct on the remaining comparison length $r$. When $r=0$, the length equation gives $i=|w_0|$. The current input symbol is $x[i]? $ by the head-position reading fact (`inputSymbol_at`). If $x=w_0$, the machine sees the end of the matching word and enters the emission chain for $u$; otherwise, it enters the chain for $v$. In the latter case, if the input had also ended at $i$, the common-prefix hypothesis would force $x=w_0$, so a genuine mismatch is available. In both cases the output remains empty through this control step, and the emission completion result (`ifEq_finish`) halts with the desired word. The chosen time is the emission length plus the control and halting steps, bounded by $\max(|u|,|v|)+2$. For the induction step, compare the symbols at position $i$. If they agree, the machine advances to comparison state $i+1$, moves its input head one place right (`moveInputPos_pos_of_ne_right`), and the common-prefix agreement extends to length $i+1$. Apply the induction hypothesis with one fewer symbol remaining, then include the comparison step; the total bound is at most $r+\max(|u|,|v|)+2$. If they disagree, then $x\ne w_0$ and the machine enters the emission chain for $v$ immediately. The same emission result supplies the required halted output, within the stated bound. In each branch, the run decomposition follows the one-step recursion for runs (`runFrom_succ_eq_step`).

**Key facts.** `Turing.FinTM.inputSymbol_at`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.FinTM.ifEq_finish`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
