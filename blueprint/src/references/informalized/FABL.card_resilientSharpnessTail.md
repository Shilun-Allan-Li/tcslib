<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/SiegenthalerSharpness.lean :: FABL.card_resilientSharpnessTail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size of the resilient sharpness tail

**Claim.** If $k<n-1$, the complement of the first $k+1$ coordinate indices among the $n$ coordinates has cardinality $n-k-1$.

**Proof.** The prefix is a subset of the full set of $n$ coordinate indices. For a subset of a finite set, the complement has cardinality equal to the cardinality of the whole set minus that of the subset. The whole set has size $n$, and the prefix has size $k+1$ by the prefix-cardinality result (card_resilientSharpnessPrefix). Therefore the complement has size $n-(k+1)=n-k-1$.

**Key facts.** `FABL.card_resilientSharpnessPrefix`.
