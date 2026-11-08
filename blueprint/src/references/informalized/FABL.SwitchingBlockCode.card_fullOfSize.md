<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.SwitchingBlockCode.card_fullOfSize -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Count of Nonzero Canonical Codes

**Claim.** For nonnegative integers $w$ and $i$, the number of canonical width-$w$ switching block codes with exactly $i$ positions and a nonzero bit assignment on those positions is $\binom{w}{i}(2^i-1)$.

**Proof.** Identify each such code with a pair consisting of its position set and the restriction of its bits to that set. The correspondence between codes and these pairs is given by `fullOfSizeEquiv`. Counting the pairs gives a sum over all $i$-element position sets; for each set $S$, there are $2^{|S|}-1$ nonzero assignments (`card_nonzero_positionBits`). Since $|S|=i$, every summand is $2^i-1$, so the sum is the number of position sets multiplied by this common value. There are $\binom{w}{i}$ such sets (`card_positionSet`), yielding the stated formula.

**Key facts.** `FABL.SwitchingBlockCode.card_nonzero_positionBits`, `FABL.SwitchingBlockCode.card_positionSet`.
