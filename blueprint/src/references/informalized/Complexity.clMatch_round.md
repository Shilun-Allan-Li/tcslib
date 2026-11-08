<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clMatch_round -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Matcher Round

**Claim.** When $j<N$, the matcher can load row $row$ from the stream and compare it with the target words in at most $l(5W+7)+2W+5$ steps, ending with that row loaded, the cursor at the end of its packed encoding, clock position $j+1$, and the corresponding comparison flag appended.

**Proof.** First use the row-loading result (`Complexity.clMatch_load`) to move from the initial search control to the comparison control, loading the row and advancing the stream cursor past its packed fields. This takes some $a\le l(5W+7)+1$ steps. Next, apply the comparison result (`Complexity.clMatch_compare`) from that configuration. It returns a Boolean flag $b$, appends it, and advances the clock, in some $b'\le 2W+3$ steps. Its characterization says that $b$ is true exactly when the two integer sums formed from the selected row fields and target fields agree; this is precisely the defining condition for the row’s comparison flag. Hence the appended flag is $\mathrm{clMatchFlag}(pos,neg,row,target)$.

There is one initial transition from the stated search configuration to the row-loading control. The clock-tick identity (`Complexity.clMatch_tick`) gives this transition, and the run composition laws (`Turing.MultiTapeTM.runFrom_succ_eq_step` and `Turing.MultiTapeTM.runFrom_add`) combine it with the loading and comparison runs. The total time is $1+a+b'\le 1+[l(5W+7)+1]+[2W+3]=l(5W+7)+2W+5$.

**Key facts.** `Complexity.clMatch_load`, `Complexity.clMatch_compare`, `Complexity.clMatch_tick`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_add`.
