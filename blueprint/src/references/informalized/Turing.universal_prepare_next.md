<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalBlock.lean :: Turing.universal_prepare_next -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor State Preparation

**Claim.** Starting from the successor-decoding phase with the table cursor at $|l|$, the interpreter reaches the record-application phase after the stated number of steps, with the successor flag, table cursor, unary state tape, and state cursor as specified.

**Proof.** Split according to whether the optional successor is absent or present.

1. If it is absent, the table has the form $l\,0\,r$, since the unary successor field has length zero. The table-reading fact says the cell at cursor $|l|$ contains $0$ (`Turing.universal_table_read`). The interpreter's transition rule for this case moves directly from successor decoding to record application, leaves the register and state tape unchanged, and advances the table cursor by zero. The one-step transition is justified by the one-step simulation lemma (`Turing.universalEval_step`); the run of length one is identified with that step and the initial configuration (`Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`).

2. If the successor is $q$, the unary field contains $q+1$ ones followed by $0$. Its first cell is therefore $1$, again by the table-reading fact. The first transition enters the state-copying phase and advances the table cursor by one. Copying the remaining unary field takes $q+1$ steps: the unary-copy lemma gives a cursor at $|l|+q+2$, a state tape encoding $q$, and a state cursor at $q+2$ (`Turing.universal_unary_copy`). The next-state transition, the copying run, and the rewind run are concatenated using the iteration laws for runs (`Turing.MultiTapeTM.runFrom_add`). The state-tape marker fact ensures that rewinding from cursor $q+2$ stops at cursor $1$ (`Turing.universalStateTape_marker` and `Turing.universal_state_rewind`), after $q+2$ steps. Together the phases take $1+(q+1)+(q+2)=2q+4$ steps. The table cursor ends at $|l|+q+1$, the state tape encodes $q$, the state cursor is $1$, and the control is record application with the non-halting flag. These are precisely the specified values because the unary successor length is $q+1$.

**Key facts.** `Turing.universal_table_read`, `Turing.universalEval_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.universal_unary_copy`, `Turing.MultiTapeTM.runFrom_add`, `Turing.universalStateTape_marker`, `Turing.universal_state_rewind`.
