<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.lenParse_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Parse-and-Compare Run

**Claim.** For any decomposition $x=ps$ and counter $r\le |c.output|$, the checker started in its parse state at position $|p|$ halts within $|s|+1$ steps and outputs the single bit that is $1$ exactly when $s$ decodes as a pair whose second component has length at most $r$.

**Proof.** Induct on the suffix $s$, using a two-symbol split when at least two symbols remain. If $s$ is empty, the checker sees no input and halts with output $0$ in one step; if $s$ is a singleton, the parser’s first step records its bit, and the next step sees the end of input and halts with output $0$. These cases agree with the recursive definition of `pairDecode` and meet the stated time bound. For $s=bds'$, the two-symbol block transition (`lenParse_block`) gives three cases. If $b=d$, the checker returns to the parse state after two steps, and the induction hypothesis on $s'$ supplies a halting run and the correct output; concatenating the initial two steps with that run uses the run-composition law (`runFrom_add`). The recursive definition of `pairDecode` shows that matching bits are prepended to the first component without changing the decoded second component. If $(b,d)=(1,0)$, the block transition already halts with output $0$, as required because this pattern is invalid for `pairDecode`. If $(b,d)=(0,1)$, the checker enters suffix comparison after two steps; the suffix-comparison result (`lenSuffix_run`) provides a halted continuation whose output tests whether the remaining suffix has length at most $r$. This is precisely the second-component length test for the decoded pair. In each continuing case, the two consumed symbols plus the inductive time bound fit within $|s|+1$.

**Key facts.** `Turing.FinTM.lenParse_block`, `Turing.FinTM.lenParse_first`, `Turing.FinTM.lenSuffix_run`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
