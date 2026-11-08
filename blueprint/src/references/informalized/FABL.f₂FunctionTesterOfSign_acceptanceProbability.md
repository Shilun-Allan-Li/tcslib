<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.f₂FunctionTesterOfSign_acceptanceProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance probability under binary encoding

**Claim.** Converting a sign-valued tester's answers to bits preserves its acceptance probability when the input function is encoded from bits to signs.

**Proof.** Expand both acceptance probabilities as expectations over the same seed distribution. For each seed, the acceptance contribution is determined by whether the tester accepts the transcript, so it suffices to show that the two transcripts give the same answers at each position. At a position whose query is absent, both transcripts contain no answer. At a queried address $x$, the binary tester converts the bit $f(x)$ to the sign $\operatorname{signEncode}(f(x))$, exactly the answer supplied to the original tester on the sign-encoded function. Thus the acceptance decisions agree for every seed, and hence so do their expectations.

**Key facts.** `FABL.NonadaptiveFunctionTester.transcript_apply`.
