<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.cont_mask_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the emission mask

**Claim.** For every finite deterministic Turing machine, input, configuration, and natural number $t$, the emission mask for the first $t$ steps has length exactly $t$.

**Proof.** Induct on $t$, generalizing the configuration. For zero steps the mask is empty, hence has length zero. For $t+1$ steps its definition prefixes one Boolean indicator to the mask for $t$ steps starting from the one-step successor. A list with one new head has length one more than its tail, and the induction hypothesis makes that tail's length $t$; thus the length is $t+1$.
