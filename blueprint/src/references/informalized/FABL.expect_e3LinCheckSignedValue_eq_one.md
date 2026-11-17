<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadLimitations.lean :: FABL.expect_e3LinCheckSignedValue_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Perfect Acceptance and Signed Value

**Claim.** If a finite random-seed tester accepts a Boolean function with probability one, then the seed average of its selected check's signed value is one.

**Proof.** Write the acceptance probability and the desired seed average as finite sums weighted by the seed probabilities. For each seed, the signed value is twice the randomized acceptance value minus one. Thus its weighted sum is twice the acceptance-probability sum minus the sum of the seed weights. The first sum is one by hypothesis; the seed weights sum to one because a probability mass function has total mass one (\texttt{pmfExpectation\_const\_one}). Hence the signed-value average is $2\cdot1-1=1$.

**Key facts.** `FABL.pmfExpectation_const_one`.
