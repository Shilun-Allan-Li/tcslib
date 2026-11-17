<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satScan_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complete Scan of an Input Suffix

**Claim.** For every Boolean word $x$, suffix $r$, prefix $p$ with $x=p++r$, and state $q$, the scanner started in state $q$ just after $p$ halts after $|r|+1$ steps and outputs $[A(\operatorname{foldl}(\delta,q,r))]$.

**Proof.** Induct on the suffix $r$. If $r$ is empty, the head is at the end of the input. The scanner’s transition on the absent input symbol emits the acceptance bit of the current state and halts, giving the stated output after one step. For the inductive case, write $r=b::r'$. The decomposition $x=p++(b::r')$ shows that the input position immediately after $p$ is within the input and that the symbol there is $b$. The one-step scanner lemma (`satScan_step`) therefore moves the head forward one position, changes the state to $\delta(q,b)$, and leaves the output empty. Apply the induction hypothesis to the remaining suffix $r'$, now with prefix $p++[b]$ and state $\delta(q,b)$. It halts after $|r'|+1$ further steps and outputs the acceptance bit of folding the transition function over $r'$ from that new state. The fold identity identifies this with the fold over $b::r'$ from $q$, and the total number of steps is $|r|+1$.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Complexity.satScan_step`.
