<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/RandomRestrictions.lean :: FABL.sum_restrictionAssignmentWeight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total Restriction Assignment Weight

**Claim.** The weights of all assignments of free, fixed-to-$1$, or fixed-to-$-1$ restrictions to the $n$ coordinates sum to $1$.

**Proof.** Sum the product weight over all restriction assignments. Since the coordinates range independently over a finite set, the finite product-sum identity factors this total into a product, one factor for each coordinate, of the sum of the three possible coordinate weights. The three coordinate weights sum to $1$ (`FABL.sum_coordRestrictionWeight`), so the product is $1^n=1$.

**Key facts.** `FABL.sum_coordRestrictionWeight`.
