<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/DictatorTesting.lean :: FABL.NonadaptiveFunctionTester.transcript_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transcript Entry Evaluation

**Claim.** For a nonadaptive function tester, the transcript at position $j$ is the value of the function at the query address chosen there, when that address exists, and is absent otherwise.

**Proof.** By definition, the transcript sends each position $j$ to the result of applying the option map of $f$ to the query address $T.queries\;seed\;j$. Thus an absent query remains absent, while a present query carrying an address $x$ becomes the value $f(x)$. The stated equality is exactly this defining equation.
