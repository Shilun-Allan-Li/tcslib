<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Main.lean :: Complexity.LogProg.ExpBFS.stp_orcN -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Step Oracle Characterization

**Claim.** The step oracle for $N$ returns true on the nested encoding of $x$ and the binary representations of $u,v,r$ exactly when the encoded pair of configurations with codes $u$ and $v$, at window size $r$, belongs to $N$’s step language.

**Proof.** By definition, the step oracle queries oracle number $2$ on the nested encoding of $x$, $u$, $v$, and $r$. The third entry of the decider family is the step language of $N$. The indicator of a set returns true exactly for elements of that set ($\mathrm{indicator\_eq\_decide}$). Therefore this query is true exactly when that nested encoding belongs to the step language, which is precisely the defining membership condition for $\mathrm{Codec.StepRel}\;N\;x\;r\;u\;v$.

**Key facts.** `Complexity.LogProg.indicator_eq_decide`.
