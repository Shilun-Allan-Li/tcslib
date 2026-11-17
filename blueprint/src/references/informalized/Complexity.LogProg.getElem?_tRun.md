<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ParsePlain.lean :: Complexity.LogProg.getElem?_tRun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The Initial Run Ends at a Non-One Entry

**Claim.** At the index equal to the length of the initial run of ones in $x$, the possibly undefined entry of $x$ is not true.

**Proof.** The initial run ends at the first entry that is not true, if such an entry exists; if the word ends there, the entry is undefined. Thus in either case the possibly undefined entry at the endpoint is not true (`takeWhile_true_end`).

**Key facts.** `Complexity.LogProg.takeWhile_true_end`.
