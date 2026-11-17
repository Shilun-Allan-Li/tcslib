<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.boolFunctionTesterOfF₂_acceptanceProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance under Boolean encoding

**Claim.** Encoding Boolean transcript answers as elements of $\mathbb{F}_2$ preserves the acceptance probability: the encoded tester on $f$ has the same acceptance probability as the original tester on the pointwise $\mathbb{F}_2$ encoding of $f$.

**Proof.** Both acceptance probabilities average the acceptance indicator over the same seed distribution. Fix a seed. The Boolean tester feeds the original acceptance rule the transcript whose answer at each query position is the queried Boolean value encoded in $\mathbb{F}_2$. By the transcript evaluation identity (\(\texttt{FABL.NonadaptiveFunctionTester.transcript_apply}\)), and because encoding commutes with the option-valued query answers, this is exactly the transcript obtained by applying the original tester to the pointwise encoded function. Therefore the acceptance indicators agree seed by seed; averaging them gives equal probabilities.

**Key facts.** `FABL.NonadaptiveFunctionTester.transcript_apply`.
