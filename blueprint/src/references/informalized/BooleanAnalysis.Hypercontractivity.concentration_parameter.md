<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/LowDegree.lean :: BooleanAnalysis.Hypercontractivity.concentration_parameter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower bound for the concentration parameter

**Claim.** If $k$ is positive and $(\sqrt{2e})^k\le t$, then $t>0$ and $t^{2/k}/e\ge2$.

**Proof.** Apply the auxiliary concentration-parameter bound with the given $k$ and $t$. It states precisely that the assumed lower bound on $t$ implies both conclusions.

**Key facts.** `BooleanAnalysis.Hypercontractivity.ConcentrationAux.concentration_parameter`.
