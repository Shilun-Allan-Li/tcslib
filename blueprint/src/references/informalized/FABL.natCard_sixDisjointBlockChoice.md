<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.natCard_sixDisjointBlockChoice -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Six Disjoint Block Choices

**Claim.** For natural numbers $n,d$, the number of ways to choose six ordered, pairwise disjoint blocks of size $d$ from an $n$-element set is $\prod_{j=0}^{5}\binom{n-jd}{d}$.

**Proof.** The general count for choosing $t$ ordered disjoint blocks from a finite set of size $m$ is $\prod_{j=0}^{t-1}\binom{m-jd}{d}$ (`natCard_disjointBlockChoices`). Apply it to the full set of $n$ elements with $t=6$; its cardinality is $n$, giving the displayed product.

**Key facts.** `FABL.natCard_disjointBlockChoices`.
