<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_catalogPrefixTM_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix machine computes concatenation

**Claim.** For every Boolean word $w$, the finite machine determined by $w$ computes the function $x\mapsto w\mathbin{++}x$ in time $|w|+|x|+1$.

**Proof.** Fix an input word $x$. The computation equivalence (\texttt{Turing.FinTM.computesInTime_iff}) reduces the claim to showing that at the stated time the machine is halted and its output is $w\mathbin{++}x$. Split the run after $|w|$ steps and apply the run decomposition law (\texttt{Turing.MultiTapeTM.runFrom_add}). The emission lemma (\texttt{Turing.FinTM.f2_catalogPrefixTM_emit}) says that this first phase writes all of $w$ and reaches state $|w|$ with the input head at position $1$. The remaining $|x|+1$ steps consist of copying the input symbols and then halting at the blank cell: the copied-prefix lemma (\texttt{Turing.FinTM.f2_catalogPrefixTM_copy}) identifies the configuration after the first $|x|$ of these steps, with output $w\mathbin{++}x$. One final transition sees the blank cell and halts without changing the output. Thus the run has the required output and is halted at exactly $|w|+|x|+1$.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.f2_catalogPrefixTM_emit`, `Turing.FinTM.f2_catalogPrefixTM_copy`.
