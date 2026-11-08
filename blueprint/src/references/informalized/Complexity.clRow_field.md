<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRow_field -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copying One Row Field

**Claim.** Starting at field $i$ in copier start control, the row machine reaches field $i+1$ in copier start control within $3|w(i)|+4$ steps, after appending the self-delimiting encoding of $w(i)$ to the record and leaving the input position, counter words, and heads unchanged.

**Proof.** The copier’s first-return result supplies a positive time $t\le 3|w(i)|+3$ at which the two-tape copier has finished encoding $w(i)$, reached copier control $4$, and left its source tape and record in the specified condition. The row machine places those two copier tapes in the slots for field $i$ and the record tape; every other counter tape remains as it was. The placement simulation lemma (`clPlaced_run`) carries the copier’s run over to the row machine, provided the copier has not entered control $4$ earlier. That proviso is exactly the no-early-return property supplied by the copier lemma. The configuration-identification lemma (`clRow_frame`) identifies the placed initial and final configurations with row configurations: the row machine is at field $i$, first in copier start control and then in control $4$, with the record extended by `pairEncode` and the other tapes and input position unchanged. One more row-machine step, from control $4$, advances the field index to $i+1$ and resets the copier control to start. This step changes no tape or head and produces no physical output. Thus the total time is $t+1$, which is positive and at most $3|w(i)|+4$.

**Key facts.** `Complexity.clCopy_first`, `Complexity.clPlaced_run`, `Complexity.clRow_frame`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`.
