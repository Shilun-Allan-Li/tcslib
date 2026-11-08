<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean :: Turing.outSummaryCode_eq_one_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Code One Characterizes Acceptance

**Claim.** The output-summary code equals $1$ exactly when the output word is the one-symbol word containing true.

**Proof.** The summary equals the accepting summary exactly when the word is $[\mathrm{true}]$ (`outSummary_eq_accept_iff`). The code map is injective (`outSummaryCode_injective`), and the accepting summary has code $1$. Thus, if the code of a word's summary is $1$, its summary must be the accepting summary. Conversely, when the word is $[\mathrm{true}]$, its summary is accepting and its code is $1$.

**Key facts.** `Turing.outSummary_eq_accept_iff`, `Turing.outSummaryCode_injective`.
