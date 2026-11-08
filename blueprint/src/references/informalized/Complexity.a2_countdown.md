<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a2_countdown -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Countdown Halting and Output Bound

**Claim.** For every input word, valid input-head position, and natural number $n$, any counter word $u$ of value $n$ can be processed from the borrow phase so that the machine halts with the initial output followed by $n$ ones, within $(n+1)(2|u|+3)$ steps.

**Proof.** Use strong induction on $n$, with the assertion quantified over the counter word and initial output. The borrow-phase analysis (a2Borrow_correct) says that after at most $2\,\mathrm{a2BorrowPos}(u)+2$ steps the machine reaches the decrement phase, with the decremented word and the success bit specified by the decrement operation. If decrement fails, the arithmetic decrement lemma (a2Debit_value) gives $a2Value(u)=0$, hence $n=0$. One further step halts, and the borrow-time bound gives the stated total bound; the output is unchanged, as required. If decrement succeeds, the same arithmetic lemma gives $a2Value((a2Debit(u)).1)+1=n$, so the decremented value is strictly less than $n$. Apply the induction hypothesis to that word, starting with the old output followed by one true bit. The decrement preserves word length (a2Debit_length), so the induction bound plus the borrow and transition steps is at most $(n+1)(2|u|+3)$. The machine's one-step transition returns from the success state to the borrow phase, and the run-composition law (runFrom_add) combines these stages. The induction output is the old output followed by one true bit and then the decremented value's many true bits; since that value is $n-1$, this is exactly the old output followed by $n$ ones.

**Key facts.** `Complexity.a2Borrow_correct`, `Complexity.a2Debit_value`, `Complexity.a2Debit_length`, `Turing.MultiTapeTM.runFrom_add`, `Turing.moveInputPos_zero`.
