<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.width_sort3DNF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width of the Reduced Sort DNF

**Claim.** The reduced DNF representation of $\mathrm{Sort}_3$ has width $2$.

**Proof.** Unfolding the specified reduced DNF and the definition of formula width reduces the claim to a finite computation: the width is the largest number of literals in any of its terms, and this maximum is $2$.

**Caveat.** The supplied informal statement describes a different DNF of width $3$, while the formal theorem and proof establish width $2$ for `sort3DNF`.
