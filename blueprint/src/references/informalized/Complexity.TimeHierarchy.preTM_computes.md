<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/CodePrefix.lean :: Complexity.TimeHierarchy.preTM_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preprocessing output and time bound

**Claim.** For every binary word $x$, the preprocessing machine outputs $\operatorname{scanPre}(x)\mathbin{++}x$ within $3|x|+5$ steps, where the scan retains agreeing successive pairs and stops at the first disagreement.

**Proof.** The scan lemma (\texttt{pre_scan}) gives a time $t_1\le |x|+1$ at which the machine has produced $\operatorname{scanPre}(x)$ and entered its rewind-start state. The timed-rewind lemma (\texttt{timed_rewind}) moves the input head back to the beginning and enters the copy state in some $r\le c_1.\mathrm{inputPos}+2$ steps, where $c_1$ is the configuration at the end of the scan. Since its input-head position is within the input, this contributes at most $|x|+3$ steps. The copy lemma (\texttt{pre_copy}) then copies all of $x$ and halts in $|x|+1$ further steps. The output is the scan output followed by $x$, hence exactly $\operatorname{scanPre}(x)\mathbin{++}x$. The total is at most $(|x|+1)+(|x|+3)+(|x|+1)=3|x|+5$. The computation-in-time characterization (\texttt{computesInTime_iff}) converts the halting state and output calculation into the computation claim, and monotonicity in the time bound (\texttt{ComputesInTime.mono}) permits the stated bound.

**Key facts.** `Complexity.TimeHierarchy.pre_scan`, `Turing.FinTM.timed_rewind`, `Complexity.TimeHierarchy.pre_copy`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.mono`.
