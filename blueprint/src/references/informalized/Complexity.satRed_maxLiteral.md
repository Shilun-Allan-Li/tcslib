<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satRed_maxLiteral -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Maximum scan of one literal

**Claim.** Starting in state $3$ just before the serialization of $(v,\mathrm{pol})$, the machine takes exactly $2v+5$ steps to return to state $3$ just after that serialization. The counter length becomes $\max(n,v+1)$, its head returns to zero, and the second tape, its head, and the output are unchanged.

**Proof.** Write the literal encoding as an initial true bit, then $v$ further true bits, then a false bit and the polarity bit. The first true bit is read in state $3$: the machine enters state $4$, advances the input head, writes a true bit at counter position zero, and moves the counter head to one. The counter-write fact (\texttt{Complexity.satRedCounter\_write}) shows that the counter length is now $\max(n,1)$.

In state $4$, the machine scans the next $v$ true bits. The unary-run scan result (\texttt{Complexity.satRed\_maxOnes}) advances the input and counter heads by $v$, leaving the counter length $\max(n,v+1)$. On reading the false delimiter, it advances the input head, changes to state $6$, and moves the counter head back one position. It then uses $v+2$ steps to return that head to zero and enter state $5$ (\texttt{Complexity.satRed\_counterBack}). A final transition advances past the polarity bit and returns to state $3$.

These stages take $1+v+1+(v+2)+1=2v+5$ steps. Each transition preserves the second tape, its head, and the output. The one-step configuration law (\texttt{Complexity.satRed\_move}) and input-position advancement fact (\texttt{Turing.moveInputPos\_pos\_of\_ne\_right}) justify the stated transitions and positions; the one-step iteration identity (\texttt{Complexity.satRed\_one}) and run-addition law combine them into the exact run.

**Key facts.** `Complexity.satRedCfg_input`, `Complexity.satRedAction_apply`, `Complexity.satRedCounter_write`, `Complexity.satRed_maxOnes`, `Complexity.satRed_move`, `Turing.moveInputPos_pos_of_ne_right`, `Complexity.satRed_counterBack`, `Complexity.satRed_one`, `Turing.MultiTapeTM.runFrom_add`.
