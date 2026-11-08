<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.FinOracleNDTM.mem_iff_exists_choiceOut -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Language membership via choice output

**Claim.** If $N$ decides $L$ relative to $O$ within $a(n^c+1)$ steps on each input, then $x\in L$ exactly when some choice word of length $2a(|x|+1)^c$ has choice output $[\mathrm{true}]$.

**Proof.** Write $t=a(|x|^c+1)$ for the decision time on $x$ and $t'=2a(|x|+1)^c$ for the proposed choice-word length. The budget inequality (`choiceBudget_le`) gives $t\leq t'$. If $x\in L$, the decision property supplies an accepting run of length $t$; acceptance is monotone in the choice-word length (`AcceptsWithin.mono`), so there is an accepting run of length $t'$. The characterization of true choice output (`choiceOut_eq_true_iff`) converts that run into a choice word with choice output $[\mathrm{true}]$. Conversely, suppose such a word $u$ of length $t'$ exists. The same characterization says its run halts with output $[\mathrm{true}]$. Since every length-$t$ run halts by the decision-time hypothesis and $t\leq |u|$, the halted-run prefix principle (`run_take_of_halted`) shows that the run on $u$ agrees with the run on its length-$t$ prefix. That prefix therefore halts with output $[\mathrm{true}]$, making it an accepting witness at time $t$; the decision property implies $x\in L$.

**Key facts.** `Turing.choiceBudget_le`, `Turing.FinOracleNDTM.AcceptsWithin.mono`, `Turing.FinOracleNDTM.choiceOut_eq_true_iff`, `Turing.OracleNDTM.runWith_append`, `Turing.OracleNDTM.runWith_of_halt`, `Turing.run_take_of_halted`.
