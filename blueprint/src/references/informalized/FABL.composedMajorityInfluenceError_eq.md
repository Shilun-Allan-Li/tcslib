<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ComposedMajorityInfluence.lean :: FABL.composedMajorityInfluenceError_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composed Majority Influence Error Identity

**Claim.** The total influence of composed majority, after subtracting $1+\frac12\sqrt{2/\pi}\sqrt{2m+1}$, equals one half of the odd-majority total influence error.

**Proof.** Replace the composed-majority total influence by $1$ plus one half of the odd-majority total influence (`totalInfluence_composedMajority`). Then express the odd-majority total influence as $\sqrt{2/\pi}\sqrt{2m+1}$ plus its error (`totalInfluence_majority_odd_eq_main_add_error`). Substituting these expressions into the definition of the composed-majority error cancels the constant and the square-root main term, leaving one half of the odd-majority error.

**Key facts.** `FABL.totalInfluence_composedMajority`, `FABL.totalInfluence_majority_odd_eq_main_add_error`.
